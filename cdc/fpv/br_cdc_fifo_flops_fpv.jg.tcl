# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
clock push_clk -from 1 -to 10 -both_edges
clock pop_clk -from 1 -to 10 -both_edges

# declare always_in system clock
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
# reset are ready at different times
assume -env {rst |-> push_rst}
assume -env {rst |-> pop_rst}
assume -env {!push_rst |=> !push_rst}
assume -env {!pop_rst |=> !pop_rst}
assume -env {s_eventually !push_rst}
assume -env {s_eventually !pop_rst}

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {push_valid push_data push_rst} push_clk
clock -rate {pop_ready pop_rst} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
#assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
#pop_rst |-> pop_valid == 'd0}

# If assertion bound - pre-condition reachable cycle >= 2:
# it's marked as "bounded_proven (auto) instead of "undetermined"
# this only affects the status report, not the proof
set_prove_inferred_target_bound on
# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
