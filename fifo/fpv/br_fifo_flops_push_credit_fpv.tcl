# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {rst | push_sender_in_reset |-> \
(credit_initial_push <= MaxCredit) && $stable(credit_initial_push)}
assume -name no_ram_rd_data_valid_during_reset {rst | push_sender_in_reset |-> ram_rd_data_valid == 'd0}
assume -name no_push_valid_during_reset {rst | push_sender_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_credit {rst | push_sender_in_reset |-> push_credit == 'd0}
assert -name fv_rst_check_pop_valid {rst | push_sender_in_reset |-> pop_valid == 'd0}

# prove command
prove -all
