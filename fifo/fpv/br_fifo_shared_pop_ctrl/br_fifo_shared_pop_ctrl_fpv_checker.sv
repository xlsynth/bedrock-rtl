// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Shared Multi-FIFO Pop Controller FPV checker
//
// Testplan
//
// Design intent:
// - Manage the pop side of a shared multi-FIFO whose storage, FIFO head pointers, and
//   per-FIFO item counts are provided by surrounding controller logic.
// - Accept a head pointer from a logical FIFO when that FIFO has storage-backed items
//   available and the pop-side read path can accept a refill request.
// - Issue data RAM read addresses through NumReadPorts shared read ports using the
//   built-in LRU arbitration policy.
// - Return RAM read data to the selected FIFO pop interface through direct cut-through
//   logic when there is no staging buffer, or through a per-FIFO staging buffer when RAM
//   read latency or registered pop outputs require buffering.
// - Generate deallocation information for entries whose head pointer has been accepted,
//   optionally registering the deallocation path.
//
// Input assumptions:
// - The external pointer manager only asserts head_valid for FIFOs that are nonempty.
// - head remains stable while head_valid is asserted and head_ready is deasserted.
// - data_ram_rd_data_valid/data_ram_rd_data follow the issued read address stream with
//   the configured RamReadLatency.
// - pop_ready obeys the no-staging-buffer integration constraint: when there is no
//   staging buffer, pop_ready holds high while waiting for pop_valid.
//
// Output behavior checked:
// - data_ram_rd_addr_valid/data_ram_rd_addr correspond to accepted head pointers.
// - pop_valid/pop_data preserve per-FIFO read data ordering and staged valid-ready stability.
// - pop_empty reflects the empty state of the external RAM plus any staged pop-side data.
// - dealloc_valid/dealloc_entry_id correspond exactly to accepted head pointers, with the
//   configured RegisterDeallocation timing.
// - Offered head pointers eventually get accepted, and accepted heads eventually produce
//   a pop handshake.
//
// Covers:
// - Multiple FIFOs contend for fewer read ports than FIFOs.
// - Each read port issues a RAM read.
// - Each FIFO produces pop data.
// - Each FIFO exercises the deallocation path.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pop_ctrl_fpv_checker #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterDeallocation = 0,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    input logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,
    input logic [NumFifos-1:0][CountWidth-1:0] ram_items,

    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,

    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);
  localparam bit HasStagingBuffer = (RamReadLatency > 0) || RegisterPopOutputs;
  localparam int FifoIdxWidth = (NumFifos <= 1) ? 1 : $clog2(NumFifos);
  localparam int MaxPending = Depth + StagingBufferDepth + (NumReadPorts * (RamReadLatency + 1));

  logic [NumFifos-1:0] head_hs;
  logic [FifoIdxWidth-1:0] fv_fifo_id;
  logic [NumReadPorts-1:0] fv_rsp_valid;

  br_fifo_shared_pop_ctrl_common_fpv_checker #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .RegisterDeallocation(RegisterDeallocation),
      .RamReadLatency(RamReadLatency)
  ) common_checker (
      .clk,
      .rst,
      .fv_fifo_id,
      .head_hs,
      .rd_fifo_id(),
      .fv_rsp_valid,
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .dealloc_valid,
      .dealloc_entry_id,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid
  );

  for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo
    // The external item count must stay inside the configured storage capacity.
    `BR_ASSUME(ram_items_in_range_a, ram_items[i] <= CountWidth'(Depth))

    // The external empty flag must agree with the external item count abstraction.
    `BR_ASSUME(ram_empty_matches_items_a, ram_empty[i] == (ram_items[i] == '0))

    // This isolated pop-controller environment has no write side, so accepted heads consume RAM items.
    `BR_ASSUME(ram_items_decrement_on_head_hs_a,
               ##1 ram_items[i] == ($past(
                   head_hs[i]
               ) ? ($past(
                   ram_items[i]
               ) - CountWidth'(1'b1)) : $past(
                   ram_items[i]
               )))

    // Downstream pop consumers must eventually make progress so staged data can drain.
    `BR_ASSUME(pop_ready_liveness_a, s_eventually pop_ready[i])

    // The head pointer source uses ready/valid semantics, so payload holds under backpressure.
    fv_valid_ready_check #(
        .Master(1),
        .PayloadWidth(AddrWidth)
    ) fv_head_valid_ready_check (
        .clk,
        .rst,
        .ready  (head_ready[i]),
        .valid  (head_valid[i]),
        .payload(head[i])
    );

    if (HasStagingBuffer) begin : gen_pop_valid_ready_check
      // The staged pop interface is a DUT ready/valid output and must hold under backpressure.
      fv_valid_ready_check #(
          .Master(0),
          .PayloadWidth(Width)
      ) fv_pop_valid_ready_check (
          .clk,
          .rst,
          .ready  (pop_ready[i]),
          .valid  (pop_valid[i]),
          .payload(pop_data[i])
      );
    end

    // A FIFO cannot report empty in the same cycle that it presents valid pop data.
    `BR_ASSERT(pop_empty_consistent_a, pop_valid[i] |-> !pop_empty[i])

    // Deadlock check: a persistent nonempty FIFO request must eventually enter the read path.
    `BR_ASSERT(head_ready_eventual_a, head_valid[i] |-> s_eventually head_ready[i])

    // Deadlock check: once a head is accepted, its data must eventually drain to the pop side.
    `BR_ASSERT(accepted_head_pop_hsk_eventual_a,
               head_hs[i] |-> s_eventually (pop_valid[i] && pop_ready[i]))

    // Exercise the pop interface for every logical FIFO.
    `BR_COVER(pop_hsk_c, pop_valid[i] && pop_ready[i])
  end

  if (!HasStagingBuffer) begin : gen_no_staging_buffer_assumptions
    for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo
      // Without a staging buffer, pop_ready feeds the request path and must hold to avoid deadlock.
      `BR_ASSUME(pop_ready_hold_a, pop_ready[i] && !pop_valid[i] |=> pop_ready[i])
    end
  end

  // Returned RAM data for the selected FIFO must leave the pop interface in FIFO order.
  // The selected FIFO can receive RAM return data from any physical read port over time,
  // so the scoreboard has one incoming chunk per RAM read port and one outgoing chunk for
  // the selected FIFO's pop stream.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(NumReadPorts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPending)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_rsp_valid),
      .incoming_data(data_ram_rd_data),
      .outgoing_vld(pop_valid[fv_fifo_id] && pop_ready[fv_fifo_id]),
      .outgoing_data(pop_data[fv_fifo_id])
  );

endmodule : br_fifo_shared_pop_ctrl_fpv_checker
