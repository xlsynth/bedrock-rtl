# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name lfsr_rst {rst}
assume -name deassert_rst {##1 !rst}
assume -name initial_state_non_zero_during_reset {rst |-> initial_state != '0}
get_design_info
array set param_list [get_design_info -list parameter]
set Period [expr {2 ** $param_list(Width) - 1}]
set GcdA $param_list(AdvanceSteps)
set GcdB $Period
while {$GcdB != 0} {
    set Remainder [expr {$GcdA % $GcdB}]
    set GcdA $GcdB
    set GcdB $Remainder
}
set EffectivePeriod [expr {$Period / $GcdA}]
set EffectivePeriodMinusOne [expr {$EffectivePeriod - 1}]

# abstract flop state, so DUT can start from any state
abstract -reset state
abstract -reset monitor.period_count
abstract -reset monitor.period_done
assume -name state_is_legal_after_reset {$fell(rst) |-> state != '0}
# The monitor counts positions in the AdvanceSteps effective cycle, not the full
# raw LFSR period. After reset abstraction, period_count must therefore start at
# one of those effective-step positions.
assume -name period_count_in_range_after_reset "\$fell(rst) |-> monitor.period_count < $EffectivePeriod"
assume -name period_done_matches_count_after_reset "\$fell(rst) |-> monitor.period_done == (monitor.period_count == $EffectivePeriodMinusOne)"

# FV won't be able to converge within 30m when width >= 9
set_prove_time_limit 30m

# prove command
prove -all
