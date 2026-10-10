# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
assume -name sender_reset_stays_deasserted {
  disable iff (rst) !push_sender_in_reset |=> !push_sender_in_reset
}

get_design_info
array set param_list [get_design_info -list parameter]
if {$param_list(EnableCoverPushSenderInReset) eq "1'b0"} {
  assume -name no_push_sender_in_reset {disable iff (rst) !push_sender_in_reset}
}

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {rst | push_sender_in_reset |-> \
(credit_initial_push <= Depth) && $stable(credit_initial_push)}
assume -name no_push_valid_during_reset {rst | push_sender_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_credit {rst | push_sender_in_reset |-> push_credit == 'd0}
assert -name fv_rst_check_pop_valid {rst | push_sender_in_reset |-> pop_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 10m

set NumReadPorts $param_list(NumReadPorts)
set Depth $param_list(Depth)
if {$Depth < 2 * $NumReadPorts} {
  cover -disable *br_ram_flops_pointer*br_ram_flops_tile.gen_multi_read_checks.all_rd_ports_active_a
}

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
assert -disable {br_fifo_shared_dynamic_flops_push_credit.br_fifo_shared_dynamic_ctrl_push_credit_inst.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# prove command
prove -all
