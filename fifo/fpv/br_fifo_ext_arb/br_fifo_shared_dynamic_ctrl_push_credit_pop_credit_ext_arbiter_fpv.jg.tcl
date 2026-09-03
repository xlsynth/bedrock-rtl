# SPDX-License-Identifier: Apache-2.0

# Startup reset may release independently at the two peer interfaces. Reassertion
# after startup is excluded: this campaign does not establish a dynamic-reset or
# in-flight traffic flushing contract.
clock clk
reset -none
assume -reset -name initial_reset {rst && push_sender_in_reset && pop_receiver_in_reset}
assume -bound 1 -name hold_initial_reset {rst && push_sender_in_reset && pop_receiver_in_reset}
assume -name release_system_reset {##1 !rst}
assume -name push_sender_reset_startup_only {!push_sender_in_reset |=> !push_sender_in_reset}
assume -name pop_receiver_reset_startup_only {!pop_receiver_in_reset |=> !pop_receiver_in_reset}

get_design_info

# The push producer remains quiet under its own reset contract. Other reset-time
# input controls are unconstrained.
assume -name no_push_during_reset {(rst || push_sender_in_reset) |-> push_valid == '0}
assume -name push_initial_credit_legal {credit_initial_push <= Depth}
assume -name push_initial_credit_static {$stable(credit_initial_push)}
assume -name push_withhold_legal {credit_withhold_push <= Depth}

array set param_list [get_design_info -list parameter]
set NumFifos $param_list(NumFifos)
set PopMaxCredits $param_list(PopMaxCredits)
set NumReadPorts $param_list(NumReadPorts)
for {set f 0} {$f < $NumFifos} {incr f} {
  assume -name pop_initial_credit_legal_$f "credit_initial_pop\[$f\] <= $PopMaxCredits"
  assume -name pop_initial_credit_static_$f "\$stable(credit_initial_pop\[$f\])"
  assume -name pop_withhold_legal_$f "credit_withhold_pop\[$f\] <= $PopMaxCredits"
}
# This top connects arb_can_grant to arb_grant. A legal grant names a request,
# which already requires pop credit, so the pop counter cannot see a decrement
# request with insufficient credit. Replace only these structurally unreachable
# generic covers with their exact complementary safety assertions. The internal
# arbiter variants have separate can_grant signals and keep the original covers.
for {set f 0} {$f < $NumFifos} {incr f} {
  set pop_counter [format {br_fifo_shared_pop_ctrl_credit_ext_arbiter_inst.gen_fifo_ram_read[%d].br_credit_counter} $f]
  # The decrement amount is tied to one in this pop controller.
  assert -name pop_decrement_has_credit_$f "(!rst && !push_sender_in_reset && !pop_receiver_in_reset && ${pop_counter}.decr_valid) |-> ${pop_counter}.available != '0"
  cover -disable "br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter.${pop_counter}.gen_cover_decr_gt_available.decr_gt_available_c"
}

set_prove_time_limit 10m
prove -all
