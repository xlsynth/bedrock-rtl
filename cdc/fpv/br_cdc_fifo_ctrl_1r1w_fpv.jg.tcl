# SPDX-License-Identifier: Apache-2.0

clock clk
clock push_clk -from 1 -to 10 -both_edges
clock pop_clk -from 1 -to 10 -both_edges
reset rst push_rst pop_rst

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {push_rst \
            push_valid \
            push_data} push_clk
clock -rate {pop_rst \
            pop_ready \
            pop_ram_rd_data_valid \
            pop_ram_rd_data} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst |-> push_valid == 'd0}

assume -name no_pop_ram_rd_data_valid_during_reset {@(posedge pop_clk) \
pop_rst |-> pop_ram_rd_data_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_ram_write_valid {@(posedge push_clk) \
push_rst |-> push_ram_wr_valid == 'd0}

assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
pop_rst |-> pop_valid == 'd0}

assert -name fv_rst_check_pop_ram_rd_addr_valid {@(posedge pop_clk) \
pop_rst |-> pop_ram_rd_addr_valid == 'd0}

# If assertion bound - pre-condition reachable cycle >= 2:
# it's marked as "bounded_proven (auto) instead of "undetermined"
# this only affects the status report, not the proof
set_prove_inferred_target_bound on
# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
