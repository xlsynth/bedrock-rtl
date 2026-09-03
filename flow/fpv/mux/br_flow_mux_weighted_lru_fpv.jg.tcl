# SPDX-License-Identifier: Apache-2.0

# clock/reset set up
clock clk
reset rst
get_design_info

array set param_list [get_design_info -list parameter]
set EnableAssertNoPushBackpressure $param_list(EnableAssertNoPushBackpressure)

# Immediate push acceptance means every grant updates priority, so a stalled
# grant cannot occur under the no-push-backpressure contract.
if {$EnableAssertNoPushBackpressure in {1 1'b1}} {
  cover -disable br_flow_mux_weighted_lru.br_arb_weighted_lru_inst.grant_without_state_update_C
}

prove -all
