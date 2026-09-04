# SPDX-License-Identifier: Apache-2.0

# Startup reset, including arbitrary peer-reset deassertion skew. Runtime reset
# reassertion is outside this environment; it is not silently treated as a drain.
clock clk
reset -none
assume -reset -name startup_reset {rst && push_sender_in_reset && pop_receiver_in_reset}
assume -bound 1 -name first_cycle_reset {rst && push_sender_in_reset && pop_receiver_in_reset}
assume -name system_reset_deasserts {##1 !rst}
assume -name push_reset_monotonic {!push_sender_in_reset |=> !push_sender_in_reset}
assume -name pop_reset_monotonic {!pop_receiver_in_reset |=> !pop_receiver_in_reset}
get_design_info

# The sender starts with zero credits and spends only credits returned by the
# DUT. Receiver-owned pop credits start at PopMaxCredits-credit_initial_pop.
assume -name no_push_in_reset {(rst || push_sender_in_reset) |-> push_valid == '0}
assume -name stable_push_initial {$stable(credit_initial_push)}
assume -name legal_push_initial {credit_initial_push <= Depth}
assume -name legal_push_withhold {credit_withhold_push <= Depth}
array set param_list [get_design_info -list parameter]
set NumFifos $param_list(NumFifos)
set PopMaxCredits $param_list(PopMaxCredits)
for {set i 0} {$i < $NumFifos} {incr i} {
  assume -name stable_pop_initial_$i "\$stable(credit_initial_pop\[$i\])"
  assume -name legal_pop_initial_$i "credit_initial_pop\[$i\] <= $PopMaxCredits"
  assume -name legal_pop_withhold_$i "credit_withhold_pop\[$i\] <= $PopMaxCredits"
}

# All checking is safety-based. Credits, withholding, and stalls need not make
# progress; covers establish useful traffic without imposing eventual service.
set_prove_time_limit 10m
prove -all
