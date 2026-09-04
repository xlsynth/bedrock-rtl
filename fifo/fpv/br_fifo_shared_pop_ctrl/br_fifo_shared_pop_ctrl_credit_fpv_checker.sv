// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Shared Multi-FIFO Pop Controller Credit FPV checker
//
// Testplan
//
// Design intent:
// - Manage the pop side of a shared multi-FIFO whose storage and FIFO head pointers are
//   provided by surrounding controller logic.
// - Track per-FIFO pop credit and issue shared RAM reads only when a FIFO has an offered
//   head pointer and available pop credit.
// - Return RAM read data on the shared per-read-port pop interface, with a binary FIFO ID
//   identifying the logical FIFO that consumed credit.
// - Generate deallocation information for accepted head pointers, optionally registering
//   the deallocation path.
//
// Input assumptions:
// - The external pointer manager only asserts head_valid for FIFOs that are nonempty.
// - head remains stable while head_valid is asserted and head_ready is deasserted.
// - data_ram_rd_data_valid/data_ram_rd_data follow the issued read address stream with
//   the configured RamReadLatency.
// - The pop credit receiver follows the Bedrock credit protocol.
//
// Output behavior checked:
// - pop_sender_in_reset follows system reset.
// - data_ram_rd_addr_valid/data_ram_rd_addr correspond to accepted head pointers.
// - pop_valid/pop_fifo_id/pop_data preserve per-FIFO read data ordering.
// - pop_empty reflects the external RAM empty state.
// - credit_count_pop/credit_available_pop obey the Bedrock credit receiver model.
// - dealloc_valid/dealloc_entry_id correspond exactly to accepted head pointers, with the
//   configured RegisterDeallocation timing.
// Reset interface properties are checked in the Jasper Tcl so they are not disabled by
// assertion macros during reset.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pop_ctrl_credit_fpv_checker #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int PopMaxCredits = 1,
    parameter bit RegisterDeallocation = 0,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CreditWidth = $clog2(PopMaxCredits + 1),
    localparam int FifoIdWidth = (NumFifos <= 1) ? 1 : $clog2(NumFifos),
    localparam int ReadPortIdWidth = (NumReadPorts <= 1) ? 1 : $clog2(NumReadPorts)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    input logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,

    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic [NumFifos-1:0] pop_credit,

    input logic [NumReadPorts-1:0] pop_valid,
    input logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    input logic [NumReadPorts-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,

    input logic [NumFifos-1:0][CreditWidth-1:0] credit_initial_pop,
    input logic [NumFifos-1:0][CreditWidth-1:0] credit_withhold_pop,
    input logic [NumFifos-1:0][CreditWidth-1:0] credit_available_pop,
    input logic [NumFifos-1:0][CreditWidth-1:0] credit_count_pop,

    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);
  localparam int MaxPending = Depth + PopMaxCredits + (NumReadPorts * (RamReadLatency + 1));

  logic [NumFifos-1:0] head_hs;
  logic [NumReadPorts-1:0][FifoIdWidth-1:0] rd_fifo_id;
  logic [FifoIdWidth-1:0] fv_fifo_id;
  // Symbolically select one physical read/pop port for the single-port data-order scoreboard.
  logic [ReadPortIdWidth-1:0] fv_read_port_id;
  logic [NumReadPorts-1:0] fv_rsp_valid;
  logic [NumReadPorts-1:0] fv_pop_rsp_valid;

  `BR_ASSUME(fv_read_port_id_range_a, $stable(fv_read_port_id) && fv_read_port_id < NumReadPorts)

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
      .rd_fifo_id,
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
    logic [NumReadPorts-1:0] fv_pop_valid_for_fifo;

    for (genvar p = 0; p < NumReadPorts; p++) begin : gen_pop_port
      assign fv_pop_valid_for_fifo[p] = pop_valid[p] && (pop_fifo_id[p] == FifoIdWidth'(i));
    end

    // The external empty flag must pass through to the per-FIFO pop empty output.
    `BR_ASSERT(pop_empty_matches_ram_empty_a, pop_empty[i] == ram_empty[i])

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

    br_pop_credit_fpv_monitor #(
        .NumPopPorts(NumReadPorts),
        .MaxCredit  (PopMaxCredits)
    ) fv_pop_credit (
        .clk,
        .rst,
        .pop_sender_in_reset,
        .pop_receiver_in_reset,
        .pop_credit(pop_credit[i]),
        .pop_valid(fv_pop_valid_for_fifo),
        .credit_initial_pop(credit_initial_pop[i]),
        .credit_withhold_pop(credit_withhold_pop[i]),
        .credit_count_pop(credit_count_pop[i]),
        .credit_available_pop(credit_available_pop[i])
    );

    // Exercise the pop interface for every logical FIFO.
    `BR_COVER(pop_valid_c, |fv_pop_valid_for_fifo)
  end

  for (genvar p = 0; p < NumReadPorts; p++) begin : gen_read_port_checks
    assign fv_pop_rsp_valid[p] = pop_valid[p] && (pop_fifo_id[p] == fv_fifo_id);

    // Pop data is a direct pass-through from the RAM response on the same physical port.
    `BR_ASSERT(pop_data_matches_ram_data_a, pop_valid[p] |-> pop_data[p] == data_ram_rd_data[p])

    // Pop valid is a direct pass-through from the RAM response valid on the same physical port.
    `BR_ASSERT(pop_valid_matches_ram_valid_a, pop_valid[p] == data_ram_rd_data_valid[p])

    if (RamReadLatency == 0) begin : gen_lat0_fifo_id
      // Pop FIFO ID must match the same-cycle read request FIFO ID.
      `BR_ASSERT(pop_fifo_id_matches_read_a, pop_valid[p] |-> pop_fifo_id[p] == rd_fifo_id[p])
    end else begin : gen_lat_non0_fifo_id
      // Pop FIFO ID must match the delayed read request FIFO ID.
      `BR_ASSERT(pop_fifo_id_matches_read_a,
                 ##1 pop_valid[p] |-> pop_fifo_id[p] == $past(rd_fifo_id[p], RamReadLatency))
    end

    // Pop FIFO ID must name a legal logical FIFO whenever pop data is valid.
    `BR_ASSERT(pop_fifo_id_in_range_a, pop_valid[p] |-> pop_fifo_id[p] < NumFifos)
  end

  // Track one arbitrary physical port for the selected FIFO. Per-port assertions above prove
  // every pop beat is a direct RAM response pass-through and has the expected FIFO ID; this
  // symbolic-port scoreboard proves the selected port preserves data order for that FIFO.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPending)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_rsp_valid[fv_read_port_id]),
      .incoming_data(data_ram_rd_data[fv_read_port_id]),
      .outgoing_vld(fv_pop_rsp_valid[fv_read_port_id]),
      .outgoing_data(pop_data[fv_read_port_id])
  );

endmodule : br_fifo_shared_pop_ctrl_credit_fpv_checker
