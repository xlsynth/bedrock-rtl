# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# limit run time to 10-mins
set_prove_time_limit 10m

array set param_list [get_design_info -list parameter]
set NumReadPorts $param_list(NumReadPorts)
set Depth $param_list(Depth)
if {$Depth < 2 * $NumReadPorts} {
  cover -disable *br_ram_flops_pointer*br_ram_flops_tile.gen_multi_read_checks.all_rd_ports_active_a
}

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
if {[llength [get_property_list -include {type assert name {br_fifo_shared_dynamic_flops.br_fifo_shared_dynamic_ctrl_inst.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}}]] > 0} {
  assert -disable {br_fifo_shared_dynamic_flops.br_fifo_shared_dynamic_ctrl_inst.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}
}

# prove command
prove -all
