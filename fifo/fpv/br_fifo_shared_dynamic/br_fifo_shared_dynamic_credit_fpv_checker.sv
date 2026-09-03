// SPDX-License-Identifier: Apache-2.0

// Shared safety checks for dynamic FIFOs with push and pop credits.
// rst is the union of system reset and both peer resets. Initial credit values
// are symbolic and stable; zero initial pop credit is legal because the receiver
// initially owns the remaining PopMaxCredits credits. There are no fairness or
// eventual-drain assumptions. The push sender starts with zero credits.
// Pushes may spend same-cycle returned credits, and a receiver may return a
// credit on the cycle the associated pop response arrives.
//
// pop_issue observes head_valid & head_ready. Credit is consumed and RAM storage
// is released at this event; data is delivered DataRamReadLatency cycles later.
// Independent occupancy and credit models check both boundaries. The symbolic
// FIFO scoreboard checks all payload bits and ascending write-port order.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_credit_fpv_checker #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int PopMaxCredits = 1,
    parameter int DataRamReadLatency = 0,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int PopCreditWidth = $clog2(PopMaxCredits + 1),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos)
) (
    input logic clk,
    // FIFO storage/scoreboard reset; protocol monitors also receive the actual
    // system reset and the separate reset signals for their own interfaces.
    input logic rst,
    input logic system_rst,
    input logic push_sender_in_reset,
    input logic push_receiver_in_reset,
    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic push_credit_stall,
    input logic [PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    input logic push_full,
    input logic [CountWidth-1:0] credit_initial_push,
    input logic [CountWidth-1:0] credit_withhold_push,
    input logic [CountWidth-1:0] credit_available_push,
    input logic [CountWidth-1:0] credit_count_push,
    input logic [NumFifos-1:0] pop_credit,
    input logic [NumReadPorts-1:0] pop_valid,
    input logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    input logic [NumReadPorts-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_initial_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_withhold_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_available_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_count_pop,
    input logic [NumFifos-1:0] pop_issue
);
  localparam int MaxPending = Depth + NumFifos * PopMaxCredits;
  localparam int StateWidth = $clog2(MaxPending + NumWritePorts + NumReadPorts + 1) + 1;
  localparam int PushCreditModelWidth = $clog2(Depth + NumWritePorts + 1) + 1;

  logic [PushCreditModelWidth-1:0] sender_credit, sender_credit_next;
  logic [StateWidth-1:0] resident_total, resident_total_next;
  logic [StateWidth-1:0] pending_total, pending_total_next;
  logic [NumFifos-1:0][NumReadPorts-1:0] response_for_fifo;
  logic [DataRamReadLatency:0][NumFifos-1:0] issue_pipe;
  logic [FifoIdWidth-1:0] fv_fifo_id;
  logic [NumWritePorts-1:0] selected_push;
  logic selected_pop;
  logic [Width-1:0] selected_data;

  br_credit_receiver_fpv_monitor #(
      .PStatic(0),
      .MaxCredit(Depth),
      .NumWritePorts(NumWritePorts),
      .UseExplicitCreditOwnership(1),
      .EnableLiveness(0)
  ) push_credit_monitor (
      .clk,
      .rst(system_rst),
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .config_base('0),
      .config_bound('0),
      .sender_credit,
      .sender_credit_next
  );

  assign resident_total_next = resident_total + StateWidth'($countones(
      push_valid
  )) - StateWidth'($countones(
      pop_issue
  ));
  assign pending_total_next = pending_total + StateWidth'($countones(
      push_valid
  )) - StateWidth'($countones(
      pop_valid
  ));
  `BR_REG(resident_total, resident_total_next)
  `BR_REG(pending_total, pending_total_next)

  `BR_ASSERT(
      push_credit_conservation_a,
      StateWidth'(sender_credit_next) + resident_total_next <= StateWidth'(credit_initial_push))
  `BR_ASSERT(resident_capacity_a, resident_total_next <= Depth)
  `BR_ASSERT(pending_capacity_a, pending_total_next <= MaxPending)
  `BR_ASSERT(issue_port_capacity_a, $countones(pop_issue) <= NumReadPorts)

  assign issue_pipe[0] = pop_issue;
  for (genvar d = 1; d <= DataRamReadLatency; d++) begin : gen_issue_delay
    `BR_REG(issue_pipe[d], issue_pipe[d-1])
  end

  for (genvar p = 0; p < NumWritePorts; p++) begin : gen_push
    `BR_ASSUME(push_fifo_id_range_a, push_valid[p] |-> push_fifo_id[p] < NumFifos)
  end
  for (genvar p = 0; p < NumReadPorts; p++) begin : gen_pop
    `BR_ASSERT(pop_fifo_id_range_a, pop_valid[p] |-> pop_fifo_id[p] < NumFifos)
  end

  for (genvar f = 0; f < NumFifos; f++) begin : gen_fifo
    logic [NumWritePorts-1:0] push_for_fifo;
    logic [StateWidth-1:0] resident, resident_next;
    localparam int PopCreditModelWidth = $clog2(PopMaxCredits + NumReadPorts + 2) + 1;
    logic [PopCreditModelWidth-1:0] available;

    for (genvar p = 0; p < NumWritePorts; p++) begin : gen_push_match
      assign push_for_fifo[p] = push_valid[p] && push_fifo_id[p] == FifoIdWidth'(f);
    end
    for (genvar p = 0; p < NumReadPorts; p++) begin : gen_pop_match
      assign response_for_fifo[f][p] = pop_valid[p] && pop_fifo_id[p] == FifoIdWidth'(f);
    end
    assign resident_next = resident + StateWidth'($countones(
        push_for_fifo
    )) - StateWidth'(pop_issue[f]);
    `BR_REG(resident, resident_next)

    br_pop_credit_fpv_monitor #(
        .NumPopPorts(NumReadPorts),
        .MaxCredit(PopMaxCredits),
        .PopCreditMaxChange(1),
        .UseExplicitCreditOwnership(1),
        .EnableLiveness(0)
    ) pop_credit_monitor (
        .clk,
        .rst(system_rst),
        .pop_sender_in_reset,
        .pop_receiver_in_reset,
        .pop_credit(pop_credit[f]),
        .pop_valid(response_for_fifo[f]),
        .pop_issue(NumReadPorts'(pop_issue[f])),
        .credit_initial_pop(credit_initial_pop[f]),
        .credit_withhold_pop(credit_withhold_pop[f]),
        .credit_count_pop(credit_count_pop[f]),
        .credit_available_pop(credit_available_pop[f]),
        .modeled_credit_count(),
        .modeled_credit_count_next(),
        .modeled_credit_available(available),
        .receiver_owned_credit(),
        .receiver_owned_credit_next()
    );

    `BR_ASSERT(issue_has_item_a, pop_issue[f] |-> resident != '0)
    `BR_ASSERT(fifo_resident_capacity_a, resident_next <= Depth)
    `BR_ASSERT(empty_matches_resident_a, pop_empty[f] == (resident == '0))
    `BR_ASSERT(one_response_per_fifo_a, $onehot0(response_for_fifo[f]))
    `BR_ASSERT(response_matches_issue_a,
               (|response_for_fifo[f]) == issue_pipe[DataRamReadLatency][f])

  end

  `BR_ASSUME(selected_fifo_range_a, $stable(fv_fifo_id) && fv_fifo_id < NumFifos)
  for (genvar p = 0; p < NumWritePorts; p++) begin : gen_selected_push
    assign selected_push[p] = push_valid[p] && push_fifo_id[p] == fv_fifo_id;
  end
  always_comb begin
    selected_pop  = 1'b0;
    selected_data = '0;
    for (int p = 0; p < NumReadPorts; p++) begin
      if (pop_valid[p] && pop_fifo_id[p] == fv_fifo_id) begin
        selected_pop = 1'b1;
        selected_data |= pop_data[p];
      end
    end
  end

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(NumWritePorts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPending)
  ) scoreboard (
      .clk,
      .rstN(!rst),
      .incoming_vld(selected_push),
      .incoming_data(push_data),
      .outgoing_vld(selected_pop),
      .outgoing_data(selected_data)
  );

endmodule : br_fifo_shared_dynamic_credit_fpv_checker
