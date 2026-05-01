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
set PeriodMinusOne [expr {2 ** $param_list(Width) - 2}]

# abstract flop state, so DUT can start from any state
abstract -reset state
abstract -reset monitor.period_count
abstract -reset monitor.period_done
assume -name state_is_legal_after_reset {$fell(rst) |-> state != '0}
assume -name period_count_matches_state_after_reset {$fell(rst) |-> monitor.period_count == state}
assume -name period_done_matches_count_after_reset "\$fell(rst) |-> monitor.period_done == (monitor.period_count == $PeriodMinusOne)"

# FV won't be able to converge within 30m when width >= 9
set_prove_time_limit 30m

# prove command
prove -all
