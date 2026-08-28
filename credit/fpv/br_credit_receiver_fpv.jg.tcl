# SPDX-License-Identifier: Apache-2.0


# Model startup with arbitrary sender reset release skew. Coordinated resets
# after traffic are outside the scope of this startup proof.
# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {rst | push_sender_in_reset |-> \
(credit_initial <= MaxCredit) && $stable(credit_initial)}
# Do not constrain push_valid/data during either reset: the receiver drops these
# transfers. The monitor uses independently qualified valids for credit accounting
# and data checks. Four-state simulation additionally checks unknown inputs.

# primary output control signal should be legal during reset
array set param_list [get_design_info -list parameter]
# Jasper reports bit parameters as sized SystemVerilog literals.
if {$param_list(RegisterPushOutputs) eq "1'b1"} {
  assert -name fv_rst_check_push_credit {rst | push_sender_in_reset |=> push_credit == 'd0}
} else {
  assert -name fv_rst_check_push_credit {rst | push_sender_in_reset |-> push_credit == 'd0}
}
assert -name fv_rst_check_pop_valid {rst | push_sender_in_reset |-> pop_valid == 'd0}

# prove command
prove -all
