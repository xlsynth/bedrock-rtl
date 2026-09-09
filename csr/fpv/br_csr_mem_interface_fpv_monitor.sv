// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL CSR Memory Interface FPV Monitor
//
// RTL behavior:
// - Translate one CSR request into one memory-word access. For writes, select
//   the memory-width data lane and byte strobes from the CSR write payload.
//   The memory address is derived separately from the CSR byte address.
// - A write completes when memory accepts the access. A read waits for memory
//   to return data/error, then replicates the memory word across the CSR read
//   data lanes and forwards the error as SLVERR. The DUT stores no RAM contents.
// - Misalignment, strobes spanning multiple memory words, and disallowed partial
//   writes produce SLVERR without accessing memory. An aligned zero-strobe write
//   succeeds without accessing memory. Address-range legality is an upstream
//   integration contract; the DUT never produces DECERR.
// - Hold a memory request stable while stalled. RegisterMemOutputs and
//   RegisterResponseOutputs select the fixed request and response latencies.
//
// Abort cancels a request only before memory accepts it. Acceptance on the abort
// edge still counts: a write takes effect, and an accepted read must still drain.
// The requester must wait for that read's CSR response pipeline to drain before
// issuing another request, even if it has aborted the original CSR transaction.
//
// What this monitor checks:
// - request_sb compares each non-bypassed CSR request's expected address,
//   direction, write data, and strobes with the actual memory handshake
//   (mem_access_valid && mem_access_ready). Cancellation before acceptance clears
//   its one queued entry; acceptance on an abort edge is still compared.
// - response_sb compares expected completion contents with EVERY CSR response.
//   Expected completions come from bypassed CSR requests, accepted memory writes,
//   or memory read returns. Read data and both response status bits are checked;
//   write-response data is ignored. Abort never clears this scoreboard.
// - Protocol assertions check request presentation and response timing, stability
//   during stalls, cancellation, and duplicate or unsolicited accesses/responses.
// - Covers exercise stalls, canceled requests followed by retries, accepted reads
//   draining after abort, writes accepted on abort, and data-lane/strobe cases.
//
// Environment assumptions use interface signals and their sampled history.
// Memory supports one outstanding accepted read and at least one cycle of read
// latency. Readiness, return delay, read data, and read error remain arbitrary
// within that contract; no memory deadline or fairness assumption is imposed.
// The checks prove completion timing once memory accepts a write or returns a
// read, without requiring memory to eventually accept or return every request.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_csr_mem_interface_fpv_monitor #(
    parameter int CsrAddrWidth = 1,
    parameter int CsrDataWidth = 32,
    parameter int MemDepth = 1,
    parameter int MemWidth = 8,
    parameter bit RegisterMemOutputs = 0,
    parameter bit RegisterResponseOutputs = 0,
    parameter bit EnablePartialWrites = 0,
    parameter bit EnableAddressRangeCheck = 1,
    localparam int CsrStrobeWidth = CsrDataWidth / 8,
    localparam int MemStrobeWidth = MemWidth / 8,
    localparam int MemAddrWidth = br_math::clamped_clog2(MemDepth)
) (
    input logic clk,
    input logic rst,
    input logic req_valid,
    input logic req_write,
    input logic [CsrAddrWidth-1:0] req_addr,
    input logic [CsrDataWidth-1:0] req_wdata,
    input logic [CsrStrobeWidth-1:0] req_wstrb,
    input logic req_abort,
    input logic resp_valid,
    input logic [CsrDataWidth-1:0] resp_rdata,
    input logic resp_slverr,
    input logic resp_decerr,
    input logic mem_access_ready,
    input logic mem_access_valid,
    input logic [MemAddrWidth-1:0] mem_access_addr,
    input logic mem_access_wr_en,
    input logic [MemWidth-1:0] mem_access_wr_data,
    input logic [MemStrobeWidth-1:0] mem_access_wr_strb,
    input logic mem_read_data_valid,
    input logic [MemWidth-1:0] mem_read_data,
    input logic mem_read_data_err
);

  localparam int NumWords = CsrDataWidth / MemWidth;
  localparam int TruncAddrWidth = MemAddrWidth + $clog2(MemStrobeWidth);
  localparam int BypassLatency = 1 + RegisterResponseOutputs;
  localparam int WriteLatency = !RegisterMemOutputs + RegisterResponseOutputs;
  localparam int RequestWidth = 1 + MemAddrWidth + MemWidth + MemStrobeWidth;
  localparam int ResponseWidth = CsrDataWidth + 2;

  logic csr_transaction_pending;
  logic memory_read_pending;

  int unsigned selected_words;
  int unsigned selected_bytes;
  int unsigned selected_word;
  logic alignment_error;
  logic multiword_error;
  logic partial_write;
  logic request_error;
  logic bypass;
  logic csr_req_valid;
  logic [MemAddrWidth-1:0] request_addr;
  logic [MemWidth-1:0] request_data;
  logic [MemStrobeWidth-1:0] request_strb;
  logic mem_access_accepted;
  logic accepted_read;
  logic accepted_write;
  logic awaiting_accept;
  logic request_canceled;
  logic held_request;
  logic first_presentation;
  logic read_transaction;
  logic bypass_request;
  logic completion_event;
  logic completion_pending;
  logic [RequestWidth-1:0] expected_request;
  logic [RequestWidth-1:0] actual_request;
  logic [ResponseWidth-1:0] expected_response;
  logic [ResponseWidth-1:0] actual_response;
  logic abort_pending_read;

  // ----------Input contracts----------
  // The DUT's one_csr_request_a integration assertion is assumed here because
  // the upstream requester is outside this unit proof.
  `BR_ASSUME(one_csr_request_a, req_valid |-> !csr_transaction_pending)
  `BR_ASSUME(no_request_with_abort_a, req_abort |-> !req_valid)

  if (!RegisterMemOutputs) begin : gen_unregistered_abort_contract
    // The child request buffer asserts pop_valid is low one cycle after abort.
    // A fresh non-bypassed request would drive it immediately in this mode.
    `BR_ASSUME(no_memory_request_after_abort_a, req_abort |=> !csr_req_valid)
  end

  // Memory returns data only for a prior accepted read. Keeping this token
  // through abort permits arbitrarily late returns, but not unsolicited ones.
  `BR_ASSUME(memory_response_has_request_a, mem_read_data_valid |-> memory_read_pending)

  // Needed only when the DUT enables its address-range integration assertion.
  // Translation checks themselves do not require a memory-word address bound.
  if (EnableAddressRangeCheck) begin : gen_builtin_address_contract
    `BR_ASSUME(address_range_a, req_addr[TruncAddrWidth-1:0] < MemDepth)
  end

  // ----------Modeling code----------
  // Decode the request independently by counting selected bytes and words.
  // Example: with 32-bit CSR data and 16-bit memory words, req_wdata = A1B2_C3D4
  // and req_wstrb = 4'b1100 select two bytes in word 1. The expected memory write
  // is data = 16'hA1B2, strobe = 2'b11. A strobe of 4'b0100 selects only one byte
  // in that word, so it is a partial write; 4'b0101 selects two different words,
  // which is rejected. The memory address comes separately from req_addr / 2;
  // the selected word identifies the CSR data lane, not the memory address.
  always_comb begin
    // No asserted strobes means zero selected bytes/words. Default the lane
    // index to zero; its payload is ignored for an empty-strobe write.
    selected_words = 0;
    selected_bytes = 0;
    selected_word  = 0;

    // Each strobe bit enables one byte (two hex digits). Count all enabled
    // bytes: for example, 4'b1100 selects two bytes, while 4'b1000 selects one.
    for (int i = 0; i < CsrStrobeWidth; i++) begin
      if (req_wstrb[i]) selected_bytes++;
    end

    // Group the byte strobes into memory-width lanes. A lane counts as selected
    // if any byte in its MemStrobeWidth-bit slice is enabled. For 32/16 widths,
    // the slices are req_wstrb[1:0] for word 0 and req_wstrb[3:2] for word 1.
    for (int i = 0; i < NumWords; i++) begin
      if (req_wstrb[i*MemStrobeWidth+:MemStrobeWidth] != '0) begin
        // More than one selected lane makes a write invalid. With exactly one
        // lane selected, selected_bytes distinguishes a full from partial write.
        selected_words++;
        // Save the lane index for extracting expected write data and strobes.
        // If several lanes are selected, this keeps the last index, but the
        // write is rejected and that lane's payload is not sent to the scoreboard.
        selected_word = i;
      end
    end
  end

  assign alignment_error = (req_addr % MemStrobeWidth) != 0;
  assign multiword_error = selected_words > 1;
  assign partial_write = selected_words == 1 && selected_bytes < MemStrobeWidth;
  assign request_error = alignment_error ||
      (req_write && (multiword_error || (!EnablePartialWrites && partial_write)));
  assign bypass = request_error || (req_write && req_wstrb == '0);
  assign csr_req_valid = req_valid && !bypass;
  assign request_addr = MemAddrWidth'(req_addr / MemStrobeWidth);
  assign request_data = req_wdata[selected_word*MemWidth+:MemWidth];
  assign request_strb = req_wstrb[selected_word*MemStrobeWidth+:MemStrobeWidth];

  // ----------Transaction events----------
  // The flags below record interface events, independently of implementation
  // retiming. Every new burst of memory valid is a first presentation; a held
  // valid is still the same request. Unexpected bursts are not filtered out.
  assign mem_access_accepted = mem_access_valid && mem_access_ready;
  assign accepted_read = mem_access_accepted && !mem_access_wr_en;
  assign accepted_write = mem_access_accepted && mem_access_wr_en;
  `BR_REG(awaiting_accept, (csr_req_valid || awaiting_accept) && !mem_access_accepted && !req_abort)
  assign request_canceled = awaiting_accept && req_abort && !mem_access_accepted;
  `BR_REG(held_request, mem_access_valid && !mem_access_ready && !req_abort)
  assign first_presentation = mem_access_valid && !held_request;
  `BR_REGL(read_transaction, !req_write && !bypass, req_valid)

  // Track outstanding CSR transactions and accepted reads for the input contracts.
  `BR_REG(csr_transaction_pending,
          req_valid || (csr_transaction_pending && !resp_valid && !request_canceled))
  `BR_REG(memory_read_pending, accepted_read || (memory_read_pending && !mem_read_data_valid))
  assign abort_pending_read = memory_read_pending && req_abort && !mem_read_data_valid;

  // Ignore write payload on reads. The address and direction are always checked.
  assign expected_request = {
    req_write,
    request_addr,
    req_write ? request_data : MemWidth'(0),
    req_write ? request_strb : MemStrobeWidth'(0)
  };
  assign actual_request = {
    mem_access_wr_en,
    mem_access_addr,
    mem_access_wr_en ? mem_access_wr_data : MemWidth'(0),
    mem_access_wr_en ? mem_access_wr_strb : MemStrobeWidth'(0)
  };

  // A completion is created by a bypass request, an accepted write, or a memory
  // read return. It stays owed until resp_valid, regardless of req_abort.
  // The scoreboard compares contents; assertions below check each event's delay.
  assign bypass_request = req_valid && bypass;
  assign completion_event = bypass_request || accepted_write || mem_read_data_valid;
  `BR_REG(completion_pending, (completion_pending || completion_event) && !resp_valid)
  assign expected_response = {
    1'b0,
    bypass_request ? request_error : (mem_read_data_valid && mem_read_data_err),
    mem_read_data_valid ? {NumWords{mem_read_data}} : CsrDataWidth'(0)
  };
  // Every response enters the scoreboard, including unsolicited responses.
  // Response data is meaningful only for a non-bypassed read transaction.
  assign actual_response = {
    resp_decerr, resp_slverr, read_transaction ? resp_rdata : CsrDataWidth'(0)
  };

  // ----------Request scoreboard and protocol----------
  // Compare CSR requests with memory handshakes. Before acceptance, abort may
  // cancel the one queued request, so clear only this scoreboard in that case.
  // Acceptance on the abort edge still consumes and checks the queued request.
  // The response scoreboard is never cleared by request cancellation.
  //
  // Example with RegisterMemOutputs = 1:
  // - Cycle 0: req_valid carries a legal, non-bypassed request. Enqueue its
  //   expected memory address, direction, write data, and strobes.
  // - Cycle 1: mem_access_valid = 1, mem_access_ready = 0. Keep the entry queued
  //   while memory stalls; presenting valid alone does not consume the entry.
  // - Cycle 2: req_abort = 1 and memory is still not ready. The request is
  //   canceled, so reset this scoreboard and discard its entry. No memory
  //   handshake or CSR completion is owed for this canceled access.
  // Alternatively, when memory accepts the request, its handshake consumes the
  // entry and must match the original CSR request. This comparison still happens
  // if req_abort is high on that same edge: accepted requests are not canceled.
  // Bypassed requests never enter this scoreboard because they need no access.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(RequestWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(1)
  ) request_sb (
      .clk(clk),
      .rstN(!rst && !request_canceled),
      .incoming_vld(csr_req_valid),
      .incoming_data(expected_request),
      .outgoing_vld(mem_access_accepted),
      .outgoing_data(actual_request)
  );

  // Check presentation timing independently of eventual memory acceptance.
  `BR_ASSERT(request_presentation_a, csr_req_valid |-> ##RegisterMemOutputs first_presentation)
  `BR_ASSERT(memory_access_owned_a, mem_access_valid |-> awaiting_accept || csr_req_valid)
  `BR_ASSERT(no_request_overwrite_a, csr_req_valid |-> !awaiting_accept)
  `BR_ASSERT(hold_stalled_request_a,
             mem_access_valid && !mem_access_ready && !req_abort |=> mem_access_valid && $stable
             (actual_request))
  `BR_ASSERT(abort_clears_request_a, req_abort |=> !mem_access_valid)
  `BR_ASSERT(bypass_has_no_memory_access_a, bypass_request |-> !mem_access_valid)

  // ----------Response scoreboard and protocol----------
  // In-order, one-entry comparison includes all response status bits. Abort is
  // deliberately absent from rstN: an accepted operation still owes completion.
  //
  // Examples of expected completions:
  // - An aligned write with zero strobes needs no memory access: expect success
  //   (SLVERR = 0). A misaligned request, multiword write, or disallowed partial
  //   write also bypasses memory, but expects SLVERR = 1 instead.
  // - A write accepted by memory creates a successful completion (SLVERR = 0).
  //   Write-response data is ignored; the memory has no write-error input.
  // - With 32-bit CSR data and 16-bit memory words, a read return of 16'hABCD
  //   creates expected CSR data 32'hABCD_ABCD. SLVERR must equal the returned
  //   mem_read_data_err: zero for success, one for a memory read error.
  // DECERR is zero for every completion, and every resp_valid consumes an entry.
  // The assertions below require the response after BypassLatency cycles from
  // a bypassed request, WriteLatency cycles from write acceptance, or
  // RegisterResponseOutputs cycles from a memory read return.
  //
  // If an accepted read is aborted while waiting for memory, its eventual return
  // still creates an expected CSR response. Do not discard it because of abort.
  // An access canceled before acceptance creates no completion entry at all.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ResponseWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(1)
  ) response_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(completion_event),
      .incoming_data(expected_response),
      .outgoing_vld(resp_valid),
      .outgoing_data(actual_response)
  );

  `BR_ASSERT(completion_events_exclusive_a, $onehot0({bypass_request, accepted_write,
                                                      mem_read_data_valid}))
  `BR_ASSERT(one_completion_pending_a, completion_event |-> !completion_pending)
  `BR_ASSERT(response_has_completion_a, resp_valid |-> completion_pending || completion_event)
  // These bounded obligations catch missing responses without assuming that
  // memory eventually accepts requests or returns read data.
  `BR_ASSERT(bypass_completion_a, bypass_request |-> ##BypassLatency resp_valid)
  `BR_ASSERT(write_completion_a, accepted_write |-> ##WriteLatency resp_valid)
  `BR_ASSERT(read_completion_a, mem_read_data_valid |-> ##RegisterResponseOutputs resp_valid)
  `BR_ASSERT(no_decode_error_a, !resp_decerr)

  // ----------End-to-end scenarios----------
  `BR_COVER(stalled_request_c,
            (mem_access_valid && !mem_access_ready && !req_abort) [* 3] ##1 mem_access_accepted)
  `BR_COVER(retry_after_canceled_request_c,
            (awaiting_accept && !mem_access_ready && req_abort) ##4 csr_req_valid)
  `BR_COVER(retry_after_abort_response_c, req_abort ##1 resp_valid ##2 req_valid)
  `BR_COVER(retry_after_aborted_read_drains_c,
            abort_pending_read ##1 mem_read_data_valid ##(RegisterResponseOutputs+2) req_valid)
  `BR_COVER(
      retry_after_read_accepted_on_abort_c,
      (accepted_read && req_abort) ##1 mem_read_data_valid ##(RegisterResponseOutputs+2) req_valid)
  `BR_COVER(write_accepted_on_abort_c, (accepted_write && req_abort) ##WriteLatency resp_valid)
  // Exercise the shorter spacing now allowed by the minimal input contract.
  `BR_COVER(next_request_after_response_c, resp_valid ##1 req_valid)
  if (RegisterMemOutputs) begin : gen_registered_retry
    `BR_COVER(next_cycle_retry_after_cancel_c, request_canceled ##1 csr_req_valid)
  end else begin : gen_unregistered_retry
    `BR_COVER(retry_after_abort_gap_c, request_canceled ##2 csr_req_valid)
  end
  `BR_COVER(empty_write_c, bypass_request && req_write && !request_error)
  `BR_COVER(read_error_c,
            (mem_read_data_valid && mem_read_data_err) ##RegisterResponseOutputs resp_valid)

  for (genvar word_idx = 0; word_idx < NumWords; word_idx++) begin : gen_write_word
    `BR_COVER(write_word_c, csr_req_valid && req_write && selected_word == word_idx)
  end
  if (MemDepth > 1 && (!EnableAddressRangeCheck || MemStrobeWidth == 1)) begin : gen_full_range
    `BR_COVER(last_word_c, mem_access_accepted && mem_access_addr == MemDepth - 1)
  end
  if (CsrAddrWidth > TruncAddrWidth) begin : gen_ignored_upper_address
    `BR_COVER(upper_address_bits_c, csr_req_valid && req_addr[CsrAddrWidth-1:TruncAddrWidth] != '0)
  end
  if (MemStrobeWidth > 1 && (!EnableAddressRangeCheck || MemDepth > 1)) begin : gen_alignment
    `BR_COVER(misaligned_request_c, req_valid && alignment_error)
  end
  if (NumWords > 1) begin : gen_multiword
    `BR_COVER(multiword_write_c, req_valid && req_write && !alignment_error && multiword_error)
  end
  if (MemStrobeWidth > 1) begin : gen_partial
    `BR_COVER(partial_write_c, req_valid && req_write && !alignment_error && partial_write)
  end

endmodule : br_csr_mem_interface_fpv_monitor

bind br_csr_mem_interface br_csr_mem_interface_fpv_monitor #(
    .CsrAddrWidth(CsrAddrWidth),
    .CsrDataWidth(CsrDataWidth),
    .MemDepth(MemDepth),
    .MemWidth(MemWidth),
    .RegisterMemOutputs(RegisterMemOutputs),
    .RegisterResponseOutputs(RegisterResponseOutputs),
    .EnablePartialWrites(EnablePartialWrites),
    .EnableAddressRangeCheck(EnableAddressRangeCheck)
) monitor (.*);
