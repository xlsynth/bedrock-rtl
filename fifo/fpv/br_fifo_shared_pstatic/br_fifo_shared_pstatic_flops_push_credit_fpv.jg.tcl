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

# primary input control signal should be legal during reset
array set param_list [get_design_info -list parameter]
set NumFifos $param_list(NumFifos)
for {set i 0} {$i < $NumFifos} {incr i} {
  assume -name initial_value_during_reset_$i "\$stable(credit_initial_push\[$i\])"
}

# limit run time to 10-mins
set_prove_time_limit 600s

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
assert -disable {br_fifo_shared_pstatic_flops_push_credit.br_fifo_shared_pstatic_ctrl_push_credit_inst.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# prove command
prove -all
