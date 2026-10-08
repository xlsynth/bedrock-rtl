// SPDX-License-Identifier: Apache-2.0

// Standalone staging-buffer FPV testplan (RTL-derived).
// - Model at most one accepted push per cycle, limited by TotalDepth. A push
//   takes the bypass when available and otherwise adds an unstaged RAM item.
//   This matches br_fifo_pop_ctrl_core and br_fifo_shared_pop_ctrl_ext_arbiter.
// - Inclusive occupancy follows the ordinary parent: a full FIFO rejects pushes
//   even when a pop occurs. RAM-only mode permits same-cycle slot replacement.
// - total_items is the pre-edge population, either inclusive of staged/inflight
//   items or RAM-only. Bypass inputs may change while not accepted.
// - Every accepted read returns exactly RamReadLatency cycles later, in order.
//   Choose arbitrary data at read issue and delay it to the RAM response; this
//   proves staging integrity, not the external RAM or its address generator.
// - Assert capacity, empty status, read eligibility, bypass eligibility, valid
//   availability, output hold, and allocation-to-pop data/order via scoreboard.
// - Cover empty/full, stall/release, read/bypass, simultaneous return/bypass,
//   issue/return overlap, and draining. No fairness is needed for safety.
// - Sweep legal buffer depths for latency 0, 1, 2, 3, 5, both occupancy modes,
//   bypass and output register settings, plus wider data and larger total depth.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_staging_buffer_fpv_monitor #(
    parameter bit EnableBypass = 1,
    parameter int TotalDepth = 3,
    parameter int RamReadLatency = 1,
    parameter int BufferDepth = RamReadLatency + 1,
    parameter int Width = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit TotalItemsIncludesStaged = 1,
    parameter bit EnableAssertPushDataKnown = 1,
    parameter bit EnableAssertFinalNotValid = 1,
    parameter bit EnableCoverSameCycleReadIssueAndReturn = 1,
    parameter bit EnableCoverBypassAndReadDataSameCycle = 1,

    localparam int TotalCountWidth  = $clog2(TotalDepth + 1),
    localparam int BufferCountWidth = $clog2(BufferDepth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [TotalCountWidth-1:0] total_items,

    input logic             bypass_ready,
    input logic             bypass_valid_unstable,
    input logic [Width-1:0] bypass_data_unstable,

    input logic             ram_rd_addr_ready,
    input logic             ram_rd_addr_valid,
    input logic             ram_rd_data_valid,
    input logic [Width-1:0] ram_rd_data,

    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,
    input logic             pop_empty
);

  // ----------FV Modeling Code----------
  // An unconstrained accepted push represents traffic from the parent FIFO.
  // Only capacity and routing constrain it; neither input data path is stable
  // unless a beat has actually been accepted.
  logic magic_push;
  logic fv_push;
  logic [Width-1:0] fv_read_data;
  logic fv_bypass_beat, fv_read_beat, fv_pop_beat;
  logic fv_ram_push;
  logic [TotalCountWidth:0] fv_total_items;
  logic [TotalCountWidth:0] fv_ram_items;
  logic [BufferCountWidth:0] fv_staged_items;
  logic [BufferCountWidth:0] fv_returned_items;
  logic fv_response_valid;
  logic [Width-1:0] fv_response_data;
  logic [Width-1:0] fv_incoming_data;
  logic fv_space_available;
  logic fv_bypass_ready;

  // Keep bypass_valid unconstrained when full: the ordinary parent forwards
  // push_valid even while push_ready is low. Inclusive mode follows its
  // push_ready = !full contract; only accepted pushes add items.
  assign fv_push = (EnableBypass ? bypass_valid_unstable : magic_push) &&
      ((fv_total_items < TotalDepth) || (!TotalItemsIncludesStaged && fv_pop_beat));
  assign fv_bypass_beat = bypass_valid_unstable && bypass_ready;
  assign fv_read_beat = ram_rd_addr_valid && ram_rd_addr_ready;
  assign fv_pop_beat = pop_valid && pop_ready;
  assign fv_ram_push = fv_push && !fv_bypass_beat;
  assign fv_incoming_data = fv_bypass_beat ? bypass_data_unstable : fv_read_data;

  `BR_REG(fv_total_items, fv_total_items + fv_push - fv_pop_beat)
  `BR_REG(fv_ram_items, fv_ram_items + fv_ram_push - fv_read_beat)
  `BR_REG(fv_staged_items, fv_staged_items + fv_read_beat + fv_bypass_beat - fv_pop_beat)
  `BR_REG(fv_returned_items, fv_returned_items + ram_rd_data_valid + fv_bypass_beat - fv_pop_beat)

  fv_delay #(
      .Width(Width + 1),
      .NumStages(RamReadLatency)
  ) read_response_delay (
      .clk,
      .rst,
      .in ({fv_read_beat, fv_read_data}),
      .out({fv_response_valid, fv_response_data})
  );

  // ----------FV assumptions----------
  if (!EnableBypass) begin : gen_no_bypass
    // Both callers tie bypass_valid low when the bypass feature is disabled.
    `BR_ASSUME(no_bypass_valid_a, !bypass_valid_unstable)
  end
  if (TotalItemsIncludesStaged) begin : gen_inclusive_count
    // The ordinary FIFO supplies its registered total population.
    `BR_ASSUME(total_items_a, total_items == TotalCountWidth'(fv_total_items))
  end else begin : gen_exclusive_count
    // The shared FIFO supplies only entries not yet issued to the RAM.
    `BR_ASSUME(total_items_a, total_items == TotalCountWidth'(fv_ram_items))
  end
  // RAM responses follow accepted requests, including zero-latency requests.
  // The output dependency is necessary to model an external request responder.
  `BR_ASSUME(read_response_valid_a, ram_rd_data_valid == fv_response_valid)
  // Each response carries the arbitrary payload selected at its issue cycle.
  `BR_ASSUME(read_response_data_a, ram_rd_data_valid |-> ram_rd_data == fv_response_data)

  // ----------Capacity and Status Checks----------
  // Accepted traffic must never overrun the total FIFO population.
  `BR_ASSERT(total_capacity_a, fv_total_items <= TotalDepth)
  // Staged includes both stored data and accepted reads still in flight.
  `BR_ASSERT(staged_capacity_a, fv_staged_items <= BufferDepth)
  // RAM reads cannot consume an entry before the parent has stored it.
  `BR_ASSERT(read_has_item_a, fv_read_beat |-> fv_ram_items != '0)
  // Both paths allocate the same staging capacity and must be mutually exclusive.
  `BR_ASSERT(single_allocation_a, !(fv_read_beat && fv_bypass_beat))
  // pop_empty reflects reserved staging slots, not just returned RAM data.
  `BR_ASSERT(pop_empty_a, pop_empty == (fv_staged_items == '0))
  // A valid output must have a returned or bypassed payload available.
  `BR_ASSERT(pop_has_data_a,
             pop_valid |-> ((fv_returned_items != '0) || ram_rd_data_valid || fv_bypass_beat))
  // Returned data cannot exceed all allocated staging slots.
  `BR_ASSERT(returned_capacity_a, fv_returned_items <= fv_staged_items)

  // ----------Read and Bypass Scheduling Checks----------
  // With nonzero latency, only previously available data can release a slot.
  assign fv_space_available = (fv_staged_items < BufferDepth) ||
      (RamReadLatency == 0 ? pop_ready : (pop_ready && pop_valid));
  assign fv_bypass_ready = EnableBypass && fv_space_available &&
      (TotalItemsIncludesStaged ?
       ((fv_total_items < BufferDepth) || ((fv_total_items == BufferDepth) && pop_ready)) :
       (fv_ram_items == '0));
  // Bypass eligibility depends on capacity and whether older RAM items remain.
  `BR_ASSERT(bypass_ready_a, bypass_ready == fv_bypass_ready)
  // Read requests must be issued whenever an older RAM item can be staged.
  `BR_ASSERT(read_valid_a,
             ram_rd_addr_valid == (fv_space_available && (fv_ram_items != '0) && !fv_bypass_ready))

  fv_valid_ready_check #(
      .Master(0),
      .PayloadWidth(Width)
  ) pop_protocol (
      .clk,
      .rst,
      .ready  (pop_ready),
      .valid  (pop_valid),
      .payload(pop_data)
  );

  // ----------Data Integrity and Ordering----------
  // Enqueue at allocation, so a newer bypass cannot overtake an older RAM read.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(BufferDepth)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_read_beat || fv_bypass_beat),
      .incoming_data(fv_incoming_data),
      .outgoing_vld(fv_pop_beat),
      .outgoing_data(pop_data)
  );

  // An allocated item must become visible after at most the RAM and output
  // register latency. This assertion needs no consumer-ready fairness.
  `BR_ASSERT(staged_progress_a,
             (fv_staged_items != '0) |-> ##[0:RamReadLatency+RegisterPopOutputs] pop_valid)

  // ----------Critical Covers----------
  `BR_COVER(staging_full_c, fv_staged_items == BufferDepth)
  `BR_COVER(total_full_c, fv_total_items == TotalDepth)
  `BR_COVER(stall_release_c, pop_valid && !pop_ready ##1 fv_pop_beat)
  `BR_COVER(fill_drain_c, fv_staged_items != '0 ##1 fv_staged_items == '0)
  `BR_COVER(read_stall_c, ram_rd_addr_valid && !ram_rd_addr_ready ##1 fv_read_beat)
  `BR_COVER(read_return_c, ram_rd_data_valid)
  if (EnableBypass) begin : gen_bypass_covers
    `BR_COVER(bypass_c, fv_bypass_beat)
    if ((RamReadLatency > 0) && (BufferDepth > RegisterPopOutputs)) begin : gen_overlap
      `BR_COVER(bypass_read_return_c, fv_bypass_beat && ram_rd_data_valid)
    end
  end
  if (BufferDepth > 1 || RamReadLatency == 0 || !RegisterPopOutputs) begin : gen_read_overlap
    `BR_COVER(read_issue_return_c, fv_read_beat && ram_rd_data_valid)
  end

endmodule : br_fifo_staging_buffer_fpv_monitor

bind br_fifo_staging_buffer br_fifo_staging_buffer_fpv_monitor #(
    .EnableBypass(EnableBypass),
    .TotalDepth(TotalDepth),
    .RamReadLatency(RamReadLatency),
    .BufferDepth(BufferDepth),
    .Width(Width),
    .RegisterPopOutputs(RegisterPopOutputs),
    .TotalItemsIncludesStaged(TotalItemsIncludesStaged),
    .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
    .EnableCoverSameCycleReadIssueAndReturn(EnableCoverSameCycleReadIssueAndReturn),
    .EnableCoverBypassAndReadDataSameCycle(EnableCoverBypassAndReadDataSameCycle)
) monitor (.*);
