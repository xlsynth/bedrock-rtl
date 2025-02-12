# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {rst | pop_receiver_in_reset |-> \
(credit_initial <= MaxCredit) && $stable(credit_initial)}
assume -name no_pop_credit_during_reset {rst | pop_receiver_in_reset |-> pop_credit == 'd0}
assume -name no_push_during_reset {rst | pop_receiver_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst | pop_receiver_in_reset |-> pop_valid == 'd0}

# prove command
prove -all
