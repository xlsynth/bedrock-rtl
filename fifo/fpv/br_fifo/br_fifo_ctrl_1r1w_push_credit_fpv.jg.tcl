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
(credit_initial_push <= MaxCredit) && $stable(credit_initial_push)}
assume -name no_ram_rd_data_valid_during_reset {rst | push_sender_in_reset |-> ram_rd_data_valid == 'd0}
assume -name no_push_valid_during_reset {rst | push_sender_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_credit {rst | push_sender_in_reset |-> push_credit == 'd0}
assert -name fv_rst_check_pop_valid {rst | push_sender_in_reset |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_wr_valid {rst | push_sender_in_reset |-> ram_wr_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {rst | push_sender_in_reset |-> ram_rd_addr_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 10m

# prove command
prove -all -time_limit 1m
prove -all -with_proven
