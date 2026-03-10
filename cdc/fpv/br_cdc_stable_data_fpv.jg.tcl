# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
clock src_clk -from 1 -to 10 -both_edges
clock dst_clk -from 1 -to 10 -both_edges

# declare always_in system clock
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
# reset are ready at different times
assume -env {rst |-> src_rst}
assume -env {rst |-> dst_rst}
assume -env {!src_rst |=> !src_rst}
assume -env {!dst_rst |=> !dst_rst}
assume -env {s_eventually !src_rst}
assume -env {s_eventually !dst_rst}

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {src_valid src_data src_rst} src_clk
clock -rate {dst_rst} dst_clk

get_design_info

# primary input control signal should be legal during reset
assume -name no_src_valid_during_reset {@(posedge src_clk) \
src_rst |-> src_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
