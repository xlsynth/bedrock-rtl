// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Multi-Transfer Register (Forward Variant)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_multi_xfer_distributor_rr_fpv_monitor #(
    // The number of symbols that can be transferred in a single cycle.
    // Must be at least 2.
    parameter int NumSymbols = 2,
    // The width of each symbol. Must be at least 1.
    parameter int SymbolWidth = 1,
    // The number of flows to distribute to. Must be at least NumSymbols.
    parameter int NumFlows = 2,
    // If 1, assert that push_sendable is 0 at the end of simulation.
    parameter bit EnableAssertFinalNotSendable = 1,
    localparam int CountWidth = $clog2(NumSymbols + 1)
) (
    input logic clk,
    input logic rst,

    input logic [CountWidth-1:0] push_sendable,
    input logic [CountWidth-1:0] push_receivable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] push_data,

    input logic [NumFlows-1:0] pop_valid,
    input logic [NumFlows-1:0] pop_ready,
    input logic [NumFlows-1:0][SymbolWidth-1:0] pop_data,

    // RTL internal signal
    logic [NumSymbols-1:0][NumFlows-1:0] grant_ordered
);

  // ----------FV modeling code----------
  logic                                   push_extra_left;
  logic [CountWidth-1:0]                  fv_pushed;
  logic [CountWidth-1:0]                  fv_popped;
  logic [NumSymbols-1:0]                  fv_push_valid;
  // pop interface adjusted based on multi-grant round-robin arbitration
  logic [  NumFlows-1:0]                  idx;
  logic [  NumFlows-1:0]                  fv_pop_valid_ready;
  logic [  NumFlows-1:0][SymbolWidth-1:0] fv_pop_data;

  assign push_extra_left = push_sendable > push_receivable;
  assign fv_pushed = push_extra_left ? push_receivable : push_sendable;
  assign fv_popped = $countones(pop_valid & pop_ready);

  // if fv_push_valid[i]=1, push_data[i] is actually pushed this cycle
  always_comb begin
    fv_push_valid = 'd0;
    for (int i = 0; i < NumSymbols; i++) begin
      if (i < fv_pushed) begin
        fv_push_valid[i] = 1'd1;
      end
    end
  end

  // based on multi-rr, assign highest-priority flow to FV pop LSB
  // br_arb_multi_rr is verified as a standlone DUT
  always_comb begin
    fv_pop_valid_ready = 'd0;
    fv_pop_data = 'd0;
    idx = 'd0;
    for (int i = 0; i < NumSymbols; i++) begin
      for (int j = 0; j < NumFlows; j++) begin
        if (grant_ordered[i][j]) begin
          fv_pop_valid_ready[idx] = pop_valid[j] & pop_ready[j];
          fv_pop_data[idx] = pop_data[j];
          idx++;
        end
      end
    end
  end

  // ----------FV assumptions----------
  `BR_ASSUME(push_receivable_range_a, push_sendable <= NumSymbols)
  `BR_ASSUME(push_receivable_increment_a, push_extra_left |=> push_sendable >= $past
                                          (push_sendable - push_receivable))
  for (genvar i = 0; i < NumSymbols; i++) begin : gen_asm
    `BR_ASSUME(push_data_shift_down_a,
               push_extra_left |=> push_data[i] == $past(push_data[i+push_receivable]))
  end

  // ----------FV assertions----------
  // push_receivable is just how many symbols can be grant this cycle
  `BR_ASSERT(push_receivable_a, push_receivable == fv_popped)

  // ----------Data integrity Check----------
  // push side will only push actual pushed data
  // pop side will check actual popped data
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(SymbolWidth),
      .IN_CHUNKS(NumSymbols),
      .OUT_CHUNKS(NumFlows),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(NumSymbols)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_push_valid),
      .incoming_data(push_data),
      .outgoing_vld(fv_pop_valid_ready),
      .outgoing_data(fv_pop_data)
  );

endmodule : br_multi_xfer_distributor_rr_fpv_monitor

bind br_multi_xfer_distributor_rr br_multi_xfer_distributor_rr_fpv_monitor #(
    .NumSymbols(NumSymbols),
    .SymbolWidth(SymbolWidth),
    .NumFlows(NumFlows),
    .EnableAssertFinalNotSendable(EnableAssertFinalNotSendable)
) monitor (.*);
