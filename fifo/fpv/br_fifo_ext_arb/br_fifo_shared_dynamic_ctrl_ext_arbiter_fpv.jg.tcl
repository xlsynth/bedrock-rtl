# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}
assume -name no_data_ram_rd_data_valid {rst |-> data_ram_rd_data_valid == 'd0}
assume -name no_ptr_ram_rd_data_valid {rst |-> ptr_ram_rd_data_valid == 'd0}
array set param_list [get_design_info -list parameter]
set NumReadPorts $param_list(NumReadPorts)
for {set i 0} {$i < $NumReadPorts} {incr i} {
  assume -name grant_onehot_during_reset_$i "\$onehot0(arb_grant\[$i\])"
}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_wr_valid {rst |-> data_ram_wr_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {rst |-> data_ram_rd_addr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_wr_valid {rst |-> ptr_ram_wr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_rd_addr_valid {rst |-> ptr_ram_rd_addr_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 600s

# The output of this flow fork will not be unstable because we constrain the
# ready to hold until valid is asserted.
# TODO(zhemao): Find a way to disable in RTL
cover -disable *br_flow_fork_head.br_flow_checks_valid_data_impl.*valid_unstable_c

# prove command
prove -all
