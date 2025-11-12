// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Multi-Transfer Interface Distributor Core

`include "br_asserts_internal.svh"
`include "br_tieoff.svh"

module br_multi_xfer_distributor_core #(
    // The number of symbols that can be transferred in a single cycle.
    // Must be at least 2.
    parameter int NumSymbols = 2,
    // The width of each symbol. Must be at least 1.
    parameter int SymbolWidth = 1,
    // The number of flows to distribute to. Must be at least NumSymbols.
    parameter int NumFlows = 2,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushDataStability = 1,
    parameter bit EnableCoverMorePopReadyThanSendable = 1,
    parameter bit EnableAssertFinalNotSendable = 1,

    localparam int CountWidth = $clog2(NumSymbols + 1)
) (
    input logic clk,
    input logic rst,

    // External-facing Ports
    input logic [CountWidth-1:0] push_sendable,
    output logic [CountWidth-1:0] push_receivable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] push_data,

    output logic [NumFlows-1:0] pop_valid,
    input logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0][SymbolWidth-1:0] pop_data,

    // Internal-facing ports
    output logic [NumFlows-1:0] request,
    output logic [CountWidth-1:0] grant_allowed,
    input logic [NumFlows-1:0] grant,
    input logic [NumSymbols-1:0][NumFlows-1:0] grant_ordered,
    input logic [CountWidth-1:0] grant_count,
    output logic enable_priority_update
);
  logic [NumFlows-1:0][NumSymbols-1:0] grant_ordered_transposed;

  for (genvar i = 0; i < NumFlows; i++) begin : gen_grant_ordered_transposed
    for (genvar j = 0; j < NumSymbols; j++) begin : gen_grant_ordered_transposed_inner
      assign grant_ordered_transposed[i][j] = grant_ordered[j][i];
    end
  end

  // Integration Assertions

  `BR_ASSERT_STATIC(legal_num_symbols_a, NumSymbols >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  `BR_ASSERT_STATIC(legal_num_flows_a, NumFlows >= NumSymbols)

  br_multi_xfer_checks_sendable_data_intg #(
      .NumSymbols(NumSymbols),
      .SymbolWidth(SymbolWidth),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertDataStability(EnableAssertPushDataStability)
  ) br_multi_xfer_checks_sendable_data_intg_push (
      .clk(clk),
      .rst(rst),
      .sendable(push_sendable),
      .receivable(push_receivable),
      .data(push_data)
  );

  if (EnableCoverMorePopReadyThanSendable) begin : gen_more_pop_ready_than_sendable_cover
    `BR_COVER_INTG(more_pop_ready_than_sendable_c, $countones(pop_ready) > push_sendable)
  end else begin : gen_no_more_pop_ready_than_sendable_assert
    `BR_ASSERT_INTG(no_more_pop_ready_than_sendable_a, $countones(pop_ready) <= push_sendable)
  end

  // Internal integration checks
  `BR_ASSERT_IMPL(grant_count_lt_allowed_a, grant_count <= grant_allowed)

  for (genvar i = 0; i < NumFlows; i++) begin : gen_grant_ordered_transposed_checks
    `BR_ASSERT_IMPL(grant_ordered_transposed_onehot_a, $onehot0(grant_ordered_transposed[i]))
  end

  if (EnableAssertFinalNotSendable) begin : gen_final_not_sendable
    `BR_ASSERT_FINAL(final_not_sendable_a, push_sendable == '0)
  end

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  logic [  NumFlows-1:0] expected_grant_from_ordered;
  logic [CountWidth-1:0] expected_count_from_grant;

  always_comb begin
    expected_grant_from_ordered = '0;
    for (int i = 0; i < NumSymbols; i++) begin
      expected_grant_from_ordered |= grant_ordered[i];
    end
  end

  always_comb begin
    expected_count_from_grant = '0;
    for (int i = 0; i < NumFlows; i++) begin
      expected_count_from_grant += grant[i];
    end
  end

  `BR_ASSERT_IMPL(grant_matches_grant_ordered_a, grant == expected_grant_from_ordered)
  `BR_ASSERT_IMPL(grant_count_matches_grant_a, grant_count == expected_count_from_grant)
`endif
`endif

  // Implementation

  assign grant_allowed = push_sendable;
  assign request = pop_ready;
  assign pop_valid = grant;
  assign push_receivable = grant_count;
  // Priority update is already qualified by grant_allowed and request.
  // Don't have any other conditions to gate it on.
  `BR_TIEOFF_ONE(enable_priority_update)

  for (genvar i = 0; i < NumFlows; i++) begin : gen_pop_data
    br_mux_onehot #(
        .NumSymbolsIn(NumSymbols),
        .SymbolWidth (SymbolWidth)
    ) br_mux_onehot_pop_data (
        .select(grant_ordered_transposed[i]),
        .in(push_data),
        .out(pop_data[i])
    );
  end

  // Implementation Checks

  `BR_ASSERT_IMPL(pop_valid_at_most_sendable_a, $countones(pop_valid) <= push_sendable)
  `BR_ASSERT_IMPL(push_receivable_at_most_ready_a, push_receivable <= $countones(pop_ready))

  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFlows),
      .Width(SymbolWidth),
      // No backpressure is possible since we only send valid when ready is true.
      .EnableCoverBackpressure(0)
  ) br_flow_checks_valid_data_impl_pop (
      .clk,
      .rst,
      .valid(pop_valid),
      .ready(pop_ready),
      .data (pop_data)
  );
endmodule
