# clock/reset set up
clock clk
clock src_clk -from 1 -to 10 -both_edges
clock dst_clk -from 1 -to 10 -both_edges

# Source and destination resets may deassert independently after system reset releases.
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
assume -env {rst |-> src_rst}
assume -env {rst |-> dst_rst}
assume -env {!src_rst |=> !src_rst}
assume -env {!dst_rst |=> !dst_rst}
assume -env {s_eventually !src_rst}
assume -env {s_eventually !dst_rst}
# Primary inputs only change with their local clock.
clock -rate {src_data src_rst} src_clk
clock -rate {dst_rst} dst_clk

get_design_info

# Destination update indication must remain low while the destination is in reset.
assert -name no_dst_updated_during_reset {@(posedge dst_clk) \
dst_rst |-> !dst_updated}

# limit run time to 10 minutes
set_prove_time_limit 600s

prove -all
