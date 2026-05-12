# SPDX-License-Identifier: Apache-2.0

# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst && pop_receiver_in_reset}
assume -bound 1 -name delay_rst {rst && pop_receiver_in_reset}
assume -name deassert_rst {##1 !rst}
assume -name pop_receiver_in_reset_stays_deasserted {!pop_receiver_in_reset |=> !pop_receiver_in_reset}

get_design_info

# primary input control signal should be legal during reset
array set param_list [get_design_info -list parameter]
set NumFifos $param_list(NumFifos)
set PopMaxCredits $param_list(PopMaxCredits)
set RegisterDeallocation $param_list(RegisterDeallocation)
for {set i 0} {$i < $NumFifos} {incr i} {
  assume -name initial_value_legal_$i "credit_initial_pop\[$i\] <= $PopMaxCredits"
  assume -name withhold_value_legal_$i "credit_withhold_pop\[$i\] <= credit_initial_pop\[$i\]"
  assume -name initial_value_during_reset_$i "\
    (rst || pop_receiver_in_reset) |-> credit_initial_pop\[$i\] <= $PopMaxCredits"
  assume -name withhold_value_during_reset_$i "(rst || pop_receiver_in_reset) |-> credit_withhold_pop\[$i\] <= credit_initial_pop\[$i\]"
}
assume -name no_head_valid_during_reset {(rst || pop_receiver_in_reset) |-> head_valid == 'd0}
assume -name no_pop_credit_during_reset {(rst || pop_receiver_in_reset) |-> pop_credit == 'd0}
assume -name no_data_ram_rd_data_valid_during_reset {(rst || pop_receiver_in_reset) |-> data_ram_rd_data_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {(rst || pop_receiver_in_reset) |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {(rst || pop_receiver_in_reset) |-> data_ram_rd_addr_valid == 'd0}
if {$RegisterDeallocation eq "1'b1"} {
  assert -name fv_rst_check_dealloc_valid_exit {$fell(rst || pop_receiver_in_reset) |-> dealloc_valid == 'd0}
} else {
  assert -name fv_rst_check_dealloc_valid {(rst || pop_receiver_in_reset) |-> dealloc_valid == 'd0}
}

# limit run time to 10-mins
set_prove_time_limit 10m

# prove command
prove -all
