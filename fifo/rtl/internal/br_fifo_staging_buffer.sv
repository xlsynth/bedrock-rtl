// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// A small-scale circular buffer to use as the pop-side staging buffer for
// a larger FIFO. To limit additional decoding logic, the read and write
// pointers are stored as onehot-encoded vectors.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"
`include "br_tieoff.svh"

module br_fifo_staging_buffer #(
    // If 1, data can be bypassed directly from push to the staging buffer.
    // Otherwise, the buffer can only be filled by reading from storage.
    parameter bit EnableBypass = 1,
    // Total depth of the FIFO, including entries in this staging buffer.
    // Must be greater than RamReadLatency + 1.
    parameter int TotalDepth = 3,
    // Latency of RAM reads. Must be >= 1.
    parameter int RamReadLatency = 1,
    // The depth of the buffer. Must be >= 1.
    parameter int BufferDepth = RamReadLatency + 1,
    // The width of the data. Must be >= 1.
    parameter int Width = 1,
    // If 1, a flow register is added to the output so that
    // valid and data come directly from registers.
    // If 0, valid and data come combinationally from the read muxing logic.
    parameter bit RegisterPopOutputs = 0,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int TotalCountWidth  = $clog2(TotalDepth + 1),
    localparam int BufferCountWidth = $clog2(BufferDepth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [TotalCountWidth-1:0] total_items,

    // ri lint_check_off INEFFECTIVE_NET
    output logic             bypass_ready,
    input  logic             bypass_valid_unstable,
    input  logic [Width-1:0] bypass_data_unstable,
    // ri lint_check_on INEFFECTIVE_NET

    input  logic             ram_rd_addr_ready,
    output logic             ram_rd_addr_valid,
    // ram_rd_addr driven externally by counter
    input  logic             ram_rd_data_valid,
    input  logic [Width-1:0] ram_rd_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);
  // ===================
  // Integration Checks
  // ===================

  `BR_ASSERT_STATIC(legal_ram_read_latency_a, RamReadLatency >= 0)
  `BR_ASSERT_STATIC(legal_total_depth_a, TotalDepth > BufferDepth)
  `BR_ASSERT_STATIC(legal_bitwidth_a, Width >= 1)
  `BR_ASSERT_STATIC(legal_buffer_depth_a, BufferDepth >= 1)

  if (RamReadLatency > 0) begin : gen_read_latency_gt_0
    `BR_ASSERT_INTG(expected_read_latency_a,
                    ##(RamReadLatency) ram_rd_data_valid == $past(
                        ram_rd_addr_valid && ram_rd_addr_ready, RamReadLatency
                    ))
  end else begin : gen_read_latency_eq_0
    `BR_ASSERT_INTG(zero_read_latency_a,
                    ram_rd_data_valid == (ram_rd_addr_valid && ram_rd_addr_ready))
  end

  // Internal integration check
  if (!EnableBypass) begin : gen_no_bypass_assert
    `BR_ASSERT_IMPL(no_bypass_valid_a, !bypass_valid_unstable)
  end

  // ===================
  // Implementation
  // ===================

  localparam int InternalDepth = BufferDepth - RegisterPopOutputs;

  // ================
  // Read Issue Logic
  // ================
  // staged_items counts the number of items either inflight from the RAM
  // or stored in this buffer.
  // Staged items must increment when read is issued or data is bypassed
  // and decrement when popped.
  logic [BufferCountWidth-1:0] staged_items;
  logic                        staged_items_incr;
  logic                        bypass_beat;
  logic                        pop_beat;
  logic                        ram_rd_addr_beat;
  // 1 if there is space available in the buffer. This is true if
  // staged_items < BufferDepth or the buffer is being popped on this cycle.
  logic                        space_available;
  // 1 if there are items in the FIFO that have yet to be staged.
  // This is true if staged_items < total_items.
  logic                        items_not_staged;
  logic                        push_valid;
  logic [           Width-1:0] push_data;

  br_counter #(
      .MaxValue(BufferDepth),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableWrap(0)
  ) br_counter (
      .clk,
      .rst,

      .reinit       (1'b0),
      .initial_value(BufferCountWidth'(1'b0)),

      .incr_valid(staged_items_incr),
      .incr      (1'b1),

      .decr_valid(pop_beat),
      .decr      (1'b1),

      .value_next(),
      .value     (staged_items)
  );

  assign pop_beat = pop_valid && pop_ready;
  assign space_available = (staged_items < BufferDepth) || pop_ready;
  assign items_not_staged = TotalCountWidth'(staged_items) < total_items;
  assign bypass_beat = bypass_valid_unstable && bypass_ready;
  assign ram_rd_addr_valid = space_available && items_not_staged && !bypass_ready;
  assign ram_rd_addr_beat = ram_rd_addr_valid && ram_rd_addr_ready;

  if (EnableBypass) begin : gen_bypass_push
    // Bypass is allowed for the first BufferDepth entries to enter the FIFO.
    assign bypass_ready = space_available && (
        (total_items < BufferDepth) ||
        ((total_items == BufferDepth) && pop_ready));
    assign push_valid = ram_rd_data_valid || bypass_beat;
    assign push_data = ram_rd_data_valid ? ram_rd_data : bypass_data_unstable;
    assign staged_items_incr = ram_rd_addr_beat || bypass_beat;
  end else begin : gen_no_bypass_push
    `BR_TIEOFF_ZERO(bypass_ready)
    assign push_valid = ram_rd_data_valid;
    assign push_data = ram_rd_data;
    assign staged_items_incr = ram_rd_addr_beat;

    `BR_UNUSED_NAMED(bypass_inputs, {bypass_beat, bypass_valid_unstable, bypass_data_unstable})
  end

  // ===================
  // Main Buffer Storage
  // ===================
  logic             internal_pop_valid;
  logic             internal_pop_ready;
  logic [Width-1:0] internal_pop_data;

  if (InternalDepth == 0) begin : gen_no_buffer
    // This can only be true if RegisterPopOutputs=1 and BufferDepth=1
    // Just pass the push_valid through to the flow register

    assign internal_pop_valid = push_valid;
    assign internal_pop_data  = push_data;

    `BR_ASSERT_IMPL(no_double_push_a, !(ram_rd_data_valid && bypass_beat))
    `BR_ASSERT_IMPL(no_push_overflow_a, push_valid |-> internal_pop_ready)
    // Only used for assertion
    `BR_UNUSED(internal_pop_ready)
  end else if (InternalDepth == 1) begin : gen_single_entry_buffer
    // In this case, we keep a single entry buffer that is filled if data is returned
    // but internal_pop_ready is not asserted.
    // Used for assertion only
    logic buffer_valid, buffer_valid_next;
    logic buffer_data_le;
    logic [Width-1:0] buffer_data, buffer_data_next;

    // We don't have to worry about bypass_valid_unstable being asserted
    // while a read is pending since the RamReadLatency must be 1.
    // If read is pending when the bypass occurred, the read must
    // have been issued in the previous cycle and the data is
    // returning on the same cycle. We just give priority to the
    // ram_rd_data and store the bypassed data in the buffer.
    assign internal_pop_valid = buffer_valid || push_valid;
    assign internal_pop_data = buffer_valid ? buffer_data : push_data;

    // The buffer is written to if
    // 1. There is a bypass or read data return when internal_pop_ready is not
    //    asserted and buffer is not occupied.
    // 2. There is a bypass or read data return when internal_pop_ready is
    //    asserted and buffer is occupied.
    // 3. There is a read data return on the same cycle as a bypass,
    //    internal_pop_ready is asserted, and buffer is not occupied
    // In the first two cases, we save either the bypass data or the read data
    // (depending on which one occured). In the third case, we save the bypass
    // data and forward the read data.
    // Getting both bypass and read data on the same cycle when the buffer is
    // occupied and internal_pop_ready is deasserted would result in data loss
    // and should not be possible.
    // The buffer is cleared if internal_pop_ready is asserted and there is no push.
    assign buffer_valid_next =
        buffer_valid ?
        (push_valid || !internal_pop_ready) :
        ((push_valid && !internal_pop_ready) || (ram_rd_data_valid && bypass_beat));
    assign buffer_data_le = buffer_valid_next && (!buffer_valid || internal_pop_ready);
    assign buffer_data_next =
        (internal_pop_ready && !buffer_valid) ? bypass_data_unstable : push_data;

    `BR_REG(buffer_valid, buffer_valid_next)
    `BR_REGL(buffer_data, buffer_data_next, buffer_data_le)

    `BR_ASSERT_IMPL(no_double_push_overflow_a,
                    (ram_rd_data_valid && bypass_beat) |-> (!buffer_valid && internal_pop_ready))
    `BR_ASSERT_IMPL(no_single_push_overflow_a, push_valid |-> (!buffer_valid || internal_pop_ready))

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
    logic buffer_rd_data;
    logic buffer_bypass_data;

    assign buffer_rd_data = ram_rd_data_valid && (buffer_valid || !internal_pop_ready);
    assign buffer_bypass_data =
        bypass_beat && (ram_rd_data_valid || buffer_valid || !internal_pop_ready);
`endif
`endif

    `BR_ASSERT_IMPL(rd_data_buffered_correctly_a,
                    buffer_rd_data |=> (buffer_valid && buffer_data == $past(ram_rd_data)))
    `BR_ASSERT_IMPL(
        bypass_data_buffered_correctly_a,
        buffer_bypass_data |=> (buffer_valid && buffer_data == $past(bypass_data_unstable)))
  end else begin : gen_circ_buffer
    // TODO(zhemao): Consider separating the pointer management logic into a standalone module
    logic [InternalDepth-1:0][Width-1:0] mem;
    // Use onehot-encoded pointers to avoid decoding logic
    logic [InternalDepth-1:0]            ptr_onehot_init;
    logic [InternalDepth-1:0]            rd_ptr_onehot;
    logic [InternalDepth-1:0]            wr_ptr_onehot;
    logic                                rd_ptr_shift_bit;
    logic                                wr_ptr_shift_bit;
    // write-en and next for each data cell
    // mem_wr_en can have up to two bits set (immediate and delayed path)
    logic [InternalDepth-1:0]            mem_wr_en;
    logic [InternalDepth-1:0][Width-1:0] mem_wr_data;
    // Data read from mem. May not be the internal_pop_data since we can do empty bypass.
    logic [        Width-1:0]            mem_rd_data;

    logic maybe_full, maybe_full_next;
    logic ptr_match;
    logic empty;
    // only used for assertion
    logic full;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
    logic advance_wr_ptr;
    logic advance_rd_ptr;

    assign ptr_match = rd_ptr_onehot == wr_ptr_onehot;
    assign full = ptr_match && maybe_full;
    assign empty = ptr_match && !maybe_full;

    // Maybe-full becomes high when there is a push without pop
    // and goes low when there is a pop without push
    assign maybe_full_next = (advance_wr_ptr == advance_rd_ptr) ? maybe_full : advance_wr_ptr;

    assign ptr_onehot_init = InternalDepth'(1'b1);
    // Left-Rotate by 1 to advance pointer
    // shift_out becomes shift in
    br_delay_shift_reg #(
        .Width(1),
        .NumStages(InternalDepth)
    ) br_delay_shift_reg_rd_ptr (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value(ptr_onehot_init),
        .value(rd_ptr_onehot),
        .shift_en(advance_rd_ptr),
        .shift_in(rd_ptr_shift_bit),
        .shift_out(rd_ptr_shift_bit)
    );

    br_delay_shift_reg #(
        .Width(1),
        .NumStages(InternalDepth)
    ) br_delay_shift_reg_wr_ptr (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value(ptr_onehot_init),
        .value(wr_ptr_onehot),
        .shift_en(advance_wr_ptr),
        .shift_in(wr_ptr_shift_bit),
        .shift_out(wr_ptr_shift_bit)
    );

    `BR_REG(maybe_full, maybe_full_next)

    // Actual storage update
    for (genvar i = 0; i < InternalDepth; i++) begin : gen_storage
      `BR_REGL(mem[i], mem_wr_data[i], mem_wr_en[i])
    end

    br_mux_onehot #(
        .NumSymbolsIn(InternalDepth),
        .SymbolWidth (Width)
    ) br_mux_onehot_mem (
        .select(rd_ptr_onehot),
        .in    (mem),
        .out   (mem_rd_data)
    );

    if (EnableBypass) begin : gen_bypass_mem_wr
      // If bypassing is enabled, wr_ptr_onehot indicates the cell that will be
      // allocated on a given cycle. If a read is issued to the storage, it should
      // be written to the buffer at the entry pointed to at allocation time.
      // Easiest way to track this is just to put the write pointer through a delay line,
      // even though this creates some additional flops.
      logic [InternalDepth-1:0] wr_ptr_onehot_d;

      br_delay_valid #(
          .Width(InternalDepth),
          .NumStages(RamReadLatency),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_delay_valid_wr_ptr_onehot (
          .clk,
          .rst,
          .in_valid        (ram_rd_addr_beat),
          .in              (wr_ptr_onehot),
          .out_valid       (),
          .out             (wr_ptr_onehot_d),
          .out_valid_stages(),
          .out_stages      ()
      );

      logic bypass_write_en;
      logic rd_data_write_en;
      logic is_first_read_data;
      logic [InternalDepth-1:0] mem_wr_en_delayed;
      logic [InternalDepth-1:0] mem_wr_en_immediate;
      logic [InternalDepth-1:0] mem_rd_en;

      // Make sure not to write data to the RAM if it is being bypassed
      // to the internal pop interface.
      // Bypass goes direct to pop if there is no data buffered or inflight and
      // internal_pop_ready is asserted
      assign bypass_write_en = bypass_beat && !(empty && internal_pop_ready);
      // Read data goes direct to pop if it was the first read issued for an empty buffer
      // and internal_pop_ready is asserted
      assign rd_data_write_en = ram_rd_data_valid && !(is_first_read_data && internal_pop_ready);
      // Write pointer advances when a read is initiated or a bypass write occurs
      assign advance_wr_ptr = ram_rd_addr_beat || bypass_write_en;
      assign mem_wr_en_immediate = bypass_write_en ? wr_ptr_onehot : '0;
      assign mem_wr_en_delayed = rd_data_write_en ? wr_ptr_onehot_d : '0;
      assign mem_wr_en = mem_wr_en_immediate | mem_wr_en_delayed;
      assign mem_rd_en = advance_rd_ptr ? rd_ptr_onehot : '0;

      for (genvar i = 0; i < InternalDepth; i++) begin : gen_mem_wr_data
        assign mem_wr_data[i] = mem_wr_en_immediate[i] ? bypass_data_unstable : ram_rd_data;
      end

      // Since the data potentially comes after the write pointer advances, we
      // can't rely on an 'empty' flag based on pointer match to tell whether
      // or not the cell at the head has valid data. Instead, keep a valid bit
      // for each cell.
      logic [InternalDepth-1:0] mem_valid, mem_valid_next;
      logic mem_valid_le;
      logic head_valid;

      // If there is a write and read to the same cell on a cycle,
      // it must be because the memory is full and the previous occupant is being replaced.
      // Therefore, write should take precedence over read.
      assign mem_valid_next = (mem_valid & ~mem_rd_en) | mem_wr_en;
      assign mem_valid_le   = advance_rd_ptr || ram_rd_data_valid || bypass_beat;

      `BR_REGL(mem_valid, mem_valid_next, mem_valid_le)

      assign head_valid = |(mem_valid & rd_ptr_onehot);
      assign is_first_read_data = !head_valid;
      // internal_pop_valid can come from the head of the buffer
      // or be bypassed directly from the read data or the bypass data
      // For bypass data, we can only do direct bypass when the buffer is empty
      assign internal_pop_valid = head_valid ||
                                  ram_rd_data_valid ||
                                  (empty && bypass_valid_unstable);
      assign internal_pop_data = head_valid ? mem_rd_data : push_data;
      // Only advance the read pointer if the write pointer was advanced
      // to provide the data currently being consumed.
      // This is true for read from the buffer or direct from read data,
      // since a slot is always allocated for a read.
      assign advance_rd_ptr = (head_valid || ram_rd_data_valid) && internal_pop_ready;

      `BR_ASSERT_IMPL(no_push_hazard_a, ~|(mem_wr_en_immediate & mem_wr_en_delayed))
      `BR_ASSERT_IMPL(no_push_overwrite_a, ~|(mem_wr_en & mem_valid & ~mem_rd_en))
      `BR_ASSERT_IMPL(bypass_to_pop_correct_address_a,
                      (!head_valid && !ram_rd_data_valid && internal_pop_valid)
                      |->
                      (bypass_valid_unstable && (wr_ptr_onehot == rd_ptr_onehot)))
      `BR_ASSERT_IMPL(rd_data_to_pop_correct_address_a,
                      (!head_valid && ram_rd_data_valid) |-> (wr_ptr_onehot_d == rd_ptr_onehot))
    end else begin : gen_nonbypass_mem_wr
      // When ram_rd_data_valid comes back, two things can happen:
      // 1. If the buffer is empty and internal_pop_ready is asserted,
      //    the data is bypassed directly to the pop interface.
      // 2. Otherwise, the data is written to the buffer.
      assign advance_wr_ptr = ram_rd_data_valid && !(empty && internal_pop_ready);
      assign mem_wr_en = advance_wr_ptr ? wr_ptr_onehot : '0;
      assign mem_wr_data = {InternalDepth{ram_rd_data}};
      assign internal_pop_valid = !empty || push_valid;
      assign internal_pop_data = empty ? push_data : mem_rd_data;
      assign advance_rd_ptr = !empty && internal_pop_ready;
    end

    // Not used in this configuration
    `BR_UNUSED(push_valid)

    `BR_ASSERT_IMPL(no_push_overflow_a, advance_wr_ptr |-> (!full || internal_pop_ready))
  end

  // ====================
  // Final Register Stage
  // ====================
  if (RegisterPopOutputs) begin : gen_pop_reg
    br_flow_reg_fwd #(
        .Width(Width),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(internal_pop_ready),
        .push_valid(internal_pop_valid),
        .push_data (internal_pop_data),
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end else begin : gen_pop_passthru
    assign pop_valid = internal_pop_valid;
    assign pop_data = internal_pop_data;
    assign internal_pop_ready = pop_ready;
  end

  // Implementation Checks
  if (EnableBypass) begin : gen_bypass_impl_checks
    `BR_ASSERT_IMPL(no_alloc_hazard_a, !(ram_rd_addr_beat && bypass_beat))
    `BR_COVER_IMPL(bypass_and_rd_data_same_cycle_c, bypass_beat && ram_rd_data_valid)
  end
endmodule
