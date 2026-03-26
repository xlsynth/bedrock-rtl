# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

array set param_list [get_design_info -list parameter]
set NumFlows $param_list(NumFlows)

# With a single flow, select is unused in br_flow_mux_select_unstable, so the
# select-instability cover and its causality checks are unreachable.
if {$NumFlows == 1} {
  cover -disable *br_flow_mux_select_unstable.gen_select_checks.gen_unstable_select.select_unstable_c
  assert -disable *br_flow_mux_select_unstable.gen_stable_push_valid_unstable_select.pop_valid_instability_caused_by_select_a
  assert -disable *br_flow_mux_select_unstable.gen_stable_push_valid_unstable_select.gen_stable_push_data.pop_data_instability_caused_by_select_a
}

prove -all
