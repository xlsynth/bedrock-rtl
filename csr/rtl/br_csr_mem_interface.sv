// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL CSR Memory Interface
//
// This module bridges the SCB interface to an external 1RW memory interface
// in which requests might be backpressured.
//
// If a request is received but the memory interface is not ready to accept it,
// the request will be buffered until either the memory accepts the request or the
// SCB requester signals the request should be aborted.
//
// This module also handles sending the response for SCB write requests so that
// the downstream memory doesn't have to. The write response will be sent after
// the write request is accepted by the memory interface.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_csr_mem_interface #(
    // Must be >= 1
    parameter int CsrAddrWidth = 1,
    // Must be either 32 or 64
    parameter int CsrDataWidth = 32,
    // Depth of the backing memory. Must be at least 1 and <= (2 ** CsrAddrWidth) / (MemWidth / 8).
    parameter int MemDepth = 1,
    // Width of the backing memory. Must be <= CsrDataWidth, >= 8, and a power of 2.
    parameter int MemWidth = 1,
    // If 1, register the downstream memory request interfaces
    // at the cost of an extra cycle of latency.
    parameter bit RegisterMemOutputs = 0,
    // If 1, register the response outputs at the cost of an extra cycle of latency.
    parameter bit RegisterResponseOutputs = 0,
    // If 1, allow partial writes to the memory.
    // If 0, partial writes will result in slverr responses.
    // TODO(zhemao): Allow the interface to perform RMW if partial write is requested
    // but memory interface doesn't support it.
    parameter bit EnablePartialWrites = 0,
    // If 1, check that the request address is in the range [0, MemDepth)
    parameter bit EnableAddressRangeCheck = 1,

    localparam int CsrStrobeWidth = CsrDataWidth / 8,
    localparam int MemStrobeWidth = MemWidth / 8,
    localparam int MemAddrWidth   = br_math::clamped_clog2(MemDepth)
) (
    input logic clk,
    input logic rst,

    input logic req_valid,
    input logic req_write,
    input logic [CsrAddrWidth-1:0] req_addr,
    input logic [CsrDataWidth-1:0] req_wdata,
    input logic [CsrStrobeWidth-1:0] req_wstrb,
    input logic req_privileged,
    input logic req_secure,
    input logic req_abort,

    output logic resp_valid,
    output logic [CsrDataWidth-1:0] resp_rdata,
    output logic resp_slverr,
    output logic resp_decerr,

    input logic mem_access_ready,
    output logic mem_access_valid,
    output logic [MemAddrWidth-1:0] mem_access_addr,
    output logic mem_access_wr_en,
    output logic [MemWidth-1:0] mem_access_wr_data,
    output logic [MemStrobeWidth-1:0] mem_access_wr_strb,

    input logic mem_read_data_valid,
    input logic [MemWidth-1:0] mem_read_data,
    input logic mem_read_data_err
);
  // Integration checks
  `BR_ASSERT_STATIC(legal_csr_addr_width_a, CsrAddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_csr_data_width_a, CsrDataWidth == 32 || CsrDataWidth == 64)
  `BR_ASSERT_STATIC(legal_mem_depth_a,
                    MemDepth >= 1 && MemDepth <= (2 ** CsrAddrWidth) / (MemWidth / 8))
  `BR_ASSERT_STATIC(legal_mem_width_a,
                    MemWidth >= 8 && MemWidth <= CsrDataWidth && br_math::is_power_of_2(MemWidth))

  // We only care about the bits that cover the memory range
  // Upper bits might be non-zero, but they aren't used for decoding at the memory itself
  localparam int TruncCsrAddrWidth = MemAddrWidth + $clog2(MemStrobeWidth);
  br_csr_checks_intg #(
      .AddrWidth(TruncCsrAddrWidth),
      .DataWidth(CsrDataWidth),
      .EnableAddressRangeCheck(EnableAddressRangeCheck),
      .AddrMin(0),
      .AddrMax(MemDepth - 1),
      // This module doesn't care about the data
      // It should be checked by the external memory
      .EnableWriteDataKnownCheck(0)
  ) br_csr_checks_intg_inst (
      .clk,
      .rst,
      .req_valid,
      .req_write,
      .req_addr(req_addr[TruncCsrAddrWidth-1:0]),
      .req_wdata,
      .req_wstrb,
      .req_secure,
      .req_privileged,
      .req_abort,
      .resp_valid
  );

  //----------------------------------------------------------------------------
  // Request handling
  //----------------------------------------------------------------------------
  localparam int NumWords = CsrDataWidth / MemWidth;
  localparam int MemBytes = MemWidth / 8;
  localparam int OffsetWidth = $clog2(MemBytes);

  logic [MemAddrWidth-1:0] req_mem_addr;
  logic [NumWords-1:0] req_word_strb;
  logic [NumWords-1:0] req_word_partial_strb;
  logic req_error_alignment;
  logic req_error_strb_too_large;
  logic req_error_strb_too_small;
  logic req_read_error;
  logic req_write_error;
  logic req_empty_strb;
  logic req_error;
  logic req_bypass;

  assign req_mem_addr = req_addr[OffsetWidth+:MemAddrWidth];

  if (MemBytes > 1) begin : gen_word_gt_byte_size
    logic [OffsetWidth-1:0] req_offset;

    assign req_offset = req_addr[OffsetWidth-1:0];
    // Error if the address is not aligned to the memory width
    assign req_error_alignment = req_offset != '0;

    for (genvar i = 0; i < NumWords; i++) begin : gen_word_strb
      assign req_word_strb[i] = |req_wstrb[i*MemBytes+:MemBytes];
      assign req_word_partial_strb[i] =
          (|req_wstrb[i*MemBytes+:MemBytes]) && !(&req_wstrb[i*MemBytes+:MemBytes]);
    end
  end else begin : gen_no_offset_check
    assign req_error_alignment = 1'b0;
    assign req_word_strb = req_wstrb;
    assign req_word_partial_strb = '0;
  end

  if (EnablePartialWrites) begin : gen_no_error_on_partial_write
    assign req_error_strb_too_small = 1'b0;
    `BR_UNUSED(req_word_partial_strb)
  end else begin : gen_error_on_partial_write
    // If partial writes are disallowed, generate an error if the byte strobes for
    // a word are partially set.
    assign req_error_strb_too_small = |req_word_partial_strb;
  end

  // Make sure strobes are only set for a single word
  always_comb begin
    req_empty_strb = 1'b1;
    req_error_strb_too_large = 1'b0;
    for (int i = 0; i < NumWords; i++) begin
      if (req_word_strb[i]) begin
        // If strobe is not empty, it means a previous word strobe was set.
        // The word strobe is thus not onehot.
        if (!req_empty_strb) begin
          req_error_strb_too_large = 1'b1;
        end
        req_empty_strb = 1'b0;
      end
    end
  end

  assign req_read_error = req_error_alignment;
  assign req_write_error =
      req_error_alignment || req_error_strb_too_small || req_error_strb_too_large;

  // Not supported currently
  `BR_UNUSED(req_privileged)
  `BR_UNUSED(req_secure)
  // MSBs are not used
  if ((OffsetWidth + MemAddrWidth) < CsrAddrWidth) begin : gen_unused_addr_msbs
    `BR_UNUSED_NAMED(req_addr_msbs, req_addr[CsrAddrWidth-1:OffsetWidth+MemAddrWidth])
  end

  assign req_error  = req_write ? req_write_error : req_read_error;
  assign req_bypass = req_error || (req_write && req_empty_strb);

  // Request data/strobe selection and buffering
  logic push_valid;
  logic [MemWidth-1:0] push_wr_data;
  logic [MemStrobeWidth-1:0] push_wr_strb;

  assign push_valid = req_valid && !req_bypass;

  br_mux_onehot #(
      .NumSymbolsIn(NumWords),
      .SymbolWidth (MemWidth)
  ) br_mux_onehot_write_data (
      .select(req_word_strb),
      .in(req_wdata),
      .out(push_wr_data)
  );

  br_mux_onehot #(
      .NumSymbolsIn(NumWords),
      .SymbolWidth (MemStrobeWidth)
  ) br_mux_onehot_write_strb (
      .select(req_word_strb),
      .in(req_wstrb),
      .out(push_wr_strb)
  );

  br_csr_request_reg #(
      .RequestWidth(MemAddrWidth + MemWidth + MemStrobeWidth + 1),
      .RegisterPopOutputs(RegisterMemOutputs)
  ) br_csr_request_reg_inst (
      .clk,
      .rst,
      .push_valid(push_valid),
      .push_abort(req_abort),
      .push_req({req_mem_addr, push_wr_data, push_wr_strb, req_write}),
      .pop_ready(mem_access_ready),
      .pop_valid(mem_access_valid),
      .pop_req({mem_access_addr, mem_access_wr_data, mem_access_wr_strb, mem_access_wr_en})
  );

  //----------------------------------------------------------------------------
  // Response handling
  //----------------------------------------------------------------------------
  logic bypass_resp_valid;
  logic read_resp_valid;
  logic write_resp_valid;
  logic bypass_resp_error;

  logic resp_valid_int;
  logic [CsrDataWidth-1:0] resp_rdata_int;
  logic resp_slverr_int;

  assign read_resp_valid = mem_read_data_valid;
  // If memory interface is not registered, we need to delay the write response by
  // one cycle to break the combinational path from req_valid to resp_valid.
  // Otherwise, the write response can be derived directly from the mem access
  // handshake, as it is already coming from registers.
  if (RegisterMemOutputs) begin : gen_no_delay_write_resp_valid
    assign write_resp_valid = mem_access_valid && mem_access_ready && mem_access_wr_en;
  end else begin : gen_delay_write_resp_valid
    `BR_REG(write_resp_valid, mem_access_valid && mem_access_ready && mem_access_wr_en)
  end

  // For bypass responses, delay by one cycle so that response isn't combinationally
  // driven by the request.
  `BR_REG(bypass_resp_valid, req_valid && req_bypass)
  `BR_REGL(bypass_resp_error, req_error, req_valid && req_bypass)

  assign resp_valid_int = bypass_resp_valid || read_resp_valid || write_resp_valid;
  // Response data can just be the mem read data replicated so that we don't need
  // to shift based on the address offset.
  // The data will be in the correct position and the unused data lanes are ignored.
  assign resp_rdata_int = {NumWords{mem_read_data}};
  // SLVERR can be based on the request or come from the memory on read.
  assign resp_slverr_int  =
      bypass_resp_valid ? bypass_resp_error :
      read_resp_valid  ? mem_read_data_err : 1'b0;

  if (RegisterResponseOutputs) begin : gen_reg_resp_out
    `BR_REG(resp_valid, resp_valid_int)
    `BR_REGL(resp_rdata, resp_rdata_int, resp_valid_int)
    `BR_REGL(resp_slverr, resp_slverr_int, resp_valid_int)
  end else begin : gen_no_reg_resp_out
    assign resp_valid  = resp_valid_int;
    assign resp_rdata  = resp_rdata_int;
    assign resp_slverr = resp_slverr_int;
  end

  // Decode errors should be handled upstream
  // ri lint_check_waive CONST_OUTPUT
  assign resp_decerr = 1'b0;

  // Implementation checks
  // Rely on the ones in the submodules.

endmodule
