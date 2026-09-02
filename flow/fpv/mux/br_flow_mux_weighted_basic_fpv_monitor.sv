// SPDX-License-Identifier: Apache-2.0


// End-to-end checks shared by the weighted LRU and RR flow muxes.
// All properties use the public flow interfaces and weight configuration.

`include "br_asserts.svh"

module br_flow_mux_weighted_basic_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter int MaxWeight = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    localparam int WeightWidth = $clog2(MaxWeight + 1)
) (
    input logic clk,
    input logic rst,
    input logic [NumFlows-1:0][WeightWidth-1:0] cfg_weight,
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic pop_ready,
    input logic pop_valid_unstable,
    input logic [Width-1:0] pop_data_unstable
);

  // The configuration is symbolic, legal, and fixed throughout the proof.
  `BR_ASSUME(cfg_weight_stable_a, $stable(cfg_weight))
  for (genvar n = 0; n < NumFlows; n++) begin : gen_weight_assumptions
    `BR_ASSUME(cfg_weight_range_a, cfg_weight[n] >= 1 && cfg_weight[n] <= MaxWeight)
  end

  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableCoverPopBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoPopBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertPopDataStability(0)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid(pop_valid_unstable),
      .pop_data (pop_data_unstable)
  );

  `BR_ASSERT(onehot_accept_a, $onehot0(push_valid & push_ready))
  `BR_ASSERT(acceptance_conservation_a,
             (|(push_valid & push_ready)) == (pop_valid_unstable && pop_ready))

  for (genvar n = 0; n < NumFlows; n++) begin : gen_flow_checks
    `BR_ASSERT(accepted_data_a,
               push_valid[n] && push_ready[n] |-> pop_data_unstable == push_data[n])
    // A continuously requesting flow must eventually be accepted. Withdrawal
    // ends the obligation when the configured interface permits it.
    `BR_ASSERT(eventual_service_a, push_valid[n] |-> s_eventually (push_ready[n] || !push_valid[n]))
    `BR_COVER(min_weight_transfer_c, cfg_weight[n] == 1 && push_valid[n] && push_ready[n])
    `BR_COVER(max_weight_transfer_c, cfg_weight[n] == MaxWeight && push_valid[n] && push_ready[n])
  end

endmodule : br_flow_mux_weighted_basic_fpv_monitor
