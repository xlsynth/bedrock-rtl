# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# limit run time to 30-mins
set_prove_time_limit 30m

# fv_fifo is a bit oversized
cover -disable *monitor.w_fifo.gen_Bypass_ast.no_push_full_a:precondition1

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
if {[llength [get_property_list -include {type assert name {br_amba_axi_shrinker.br_flow_fork_aw.br_flow_fork_select_multihot.always_ready_when_unselected_a}}]] > 0} {
  assert -disable {br_amba_axi_shrinker.br_flow_fork_aw.br_flow_fork_select_multihot.always_ready_when_unselected_a}
}

# prove command
prove -all
