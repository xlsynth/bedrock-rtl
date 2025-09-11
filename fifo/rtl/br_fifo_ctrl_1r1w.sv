// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_fifo_ctrl_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then bypasses push-to-pop when the FIFO is empty, resulting in
    // a cut-through latency of 0 cycles, but at the cost of worse timing.
    // If 0, then pushes always go through the RAM before they can become
    // visible at the pop interface. This results in a cut-through latency of
    // 1 cycle, but timing is improved.
    parameter bit EnableBypass = 1,
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional cycle of cut-through latency.
    // If 0, pop_valid/pop_data can come directly from the push interface
    // (if bypass is enabled), the RAM read interface, and/or an internal staging
    // buffer (if RAM read latency is >0).
    parameter bit RegisterPopOutputs = 0,
    // The number of cycles between when ram_rd_addr_valid is asserted and
    // ram_rd_data_valid is asserted.
    parameter int RamReadLatency = 0,
    // The actual depth of the RAM. This may be smaller than the FIFO depth
    // if EnableBypass is 1 and RamReadLatency is >0 or RegisterPopOutputs is 1.
    // The minimum RAM depth would be (Depth - RamReadLatency - 1) or 1
    // if Depth is less than or equal to RamReadLatency + 1.
    // If bypass is disabled or RamReadLatency and RegisterPopOutputs are both 0,
    // the minimum RAM depth is Depth.
    // The RAM depth may be made larger than the minimum if convenient (e.g. the
    // backing RAM is an SRAM of slightly larger depth than the FIFO depth).
    parameter int RamDepth = Depth,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = br_math::clamped_clog2(RamDepth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Pop-side interface
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Push-side status flags
    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    output logic                  empty,
    output logic                  empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next,

    // 1R1W RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    input  logic                 ram_rd_data_valid,
    input  logic [    Width-1:0] ram_rd_data
);
  // Right now, we assume that data can be read the cycle after the
  // write for it is issued.
  // TODO(zhemao): Find a way to deal with longer hazard latencies
  // if we ever get RAMs that have it.
  localparam int ReadAfterWriteHazardLatency = 1;
  // Cut-through latency is the number of cycles between push_valid and pop_valid
  // when the FIFO is initially empty.
  localparam int CutThroughLatency =
      EnableBypass ? 32'(RegisterPopOutputs)
                   : (RamReadLatency + RegisterPopOutputs + ReadAfterWriteHazardLatency);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic bypass_ready;
  logic bypass_valid_unstable;
  logic [Width-1:0] bypass_data_unstable;

  logic push_beat;
  logic pop_beat;

  br_fifo_push_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RamDepth(RamDepth),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_push_ctrl (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .bypass_ready,
      // Bypass is only used when EnableBypass is 1.
      .bypass_valid_unstable,  // ri lint_check_waive CONST_ASSIGN
      .bypass_data_unstable,  // ri lint_check_waive CONST_ASSIGN
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .push_beat,
      .pop_beat
  );

  br_fifo_pop_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamDepth(RamDepth),
      .RamReadLatency(RamReadLatency),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_pop_ctrl (
      .clk,
      .rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty,
      .empty_next,
      .items,
      .items_next,
      // Bypass is only used when EnableBypass is 1.
      .bypass_ready,  // ri lint_check_waive CONST_ASSIGN
      .bypass_valid_unstable,
      .bypass_data_unstable,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data,
      .push_beat,
      .pop_beat
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (CutThroughLatency == 0) begin : gen_zero_lat_impl_checks
    // Check that the datapath actually has 0 cycle cut-through delay when empty.
    `BR_ASSERT_IMPL(cutthrough_0_delay_a,
                    push_valid && empty |-> pop_valid && pop_data == push_data)
    `BR_ASSERT_IMPL(pop_valid_when_not_empty_or_push_valid_a, pop_valid == (!empty || push_valid))
  end else begin : gen_nonzero_lat_impl_checks
    // Check that the datapath has the expected cut-through delay when empty.
    `BR_ASSERT_IMPL(cutthrough_delay_a,
                    push_valid && empty |-> ##(CutThroughLatency) pop_valid && pop_data == $past(
                        push_data, CutThroughLatency
                    ))
    `BR_ASSERT_IMPL(no_pop_valid_when_empty_a, empty |-> !pop_valid)
  end

  // Check that the backpressure path has 1 cycle delay.
  `BR_ASSERT_IMPL(push_backpressure_when_full_a, full |-> !push_ready)
  `BR_ASSERT_IMPL(backpressure_latency_1_cycle_a, full && pop_ready |=> !full && push_ready)

  // Flag coherence
  `BR_ASSERT_IMPL(items_plus_slots_a, items + slots == Depth)
  `BR_ASSERT_IMPL(items_next_plus_slots_next_a, items_next + slots_next == Depth)
  `BR_ASSERT_IMPL(push_and_pop_flags_unchanged_a,
                  push_beat && pop_beat |-> items_next == items && slots_next == slots)

endmodule : br_fifo_ctrl_1r1w
