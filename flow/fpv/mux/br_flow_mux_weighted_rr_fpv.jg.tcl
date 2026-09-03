# SPDX-License-Identifier: Apache-2.0

# clock/reset set up
clock clk
reset rst
get_design_info

array set param_list [get_design_info -list parameter]
set EnableAssertNoPushBackpressure $param_list(EnableAssertNoPushBackpressure)
set NumFlows $param_list(NumFlows)
set UsePairwiseArb $param_list(UsePairwiseArb)

# Immediate push acceptance means every grant updates priority, so a stalled
# grant cannot occur under the no-push-backpressure contract. The single-flow
# implementation does not contain these arbiter covers.
if {$EnableAssertNoPushBackpressure in {1 1'b1} && $NumFlows > 1} {
  if {$UsePairwiseArb in {1 1'b1}} {
    cover -disable br_flow_mux_weighted_rr.br_arb_weighted_rr_inst.gen_n_req.gen_pairwise_arb.grant_without_state_update_C
  } else {
    cover -disable br_flow_mux_weighted_rr.br_arb_weighted_rr_inst.gen_n_req.gen_unrolled_arb.br_arb_pri_rr_inst.grant_without_state_update_C
    # At most one input can be accepted per cycle, so immediate acceptance also
    # rules out simultaneous requests to the unrolled arbiter.
    cover -disable br_flow_mux_weighted_rr.br_arb_weighted_rr_inst.gen_n_req.gen_unrolled_arb.br_arb_pri_rr_inst.request_multihot_c
  }
}

prove -all
