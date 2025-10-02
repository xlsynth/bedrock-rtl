# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
clock push_clk -from 1 -to 10 -both_edges
clock pop_clk -from 1 -to 10 -both_edges

reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
assume -env {rst == push_rst}
assume -env {rst == pop_rst}

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {push_rst \
            push_sender_in_reset \
            push_credit_stall \
            push_valid \
            push_data \
            credit_initial_push \
            credit_withhold_push} push_clk
clock -rate {pop_rst \
            pop_ready \
            pop_ram_rd_data_valid \
            pop_ram_rd_data} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> \
(credit_initial_push <= Depth) && $stable(credit_initial_push)}

assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> push_valid == 'd0}

assume -name no_pop_ram_rd_data_valid_during_reset {@(posedge pop_clk) \
pop_rst |-> pop_ram_rd_data_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_credit {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> push_credit == 'd0}

assert -name fv_rst_check_push_ram_write_valid {@(posedge push_clk) \
push_rst | push_sender_in_reset  |-> push_ram_wr_valid == 'd0}

assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
pop_rst |-> pop_valid == 'd0}

assert -name fv_rst_check_pop_ram_rd_addr_valid {@(posedge pop_clk) \
pop_rst |-> pop_ram_rd_addr_valid == 'd0}

# disable cdc_fifo_basic_fpv_monitor assertions don't apply to DUT
# no push_ready signal in push credit interface
assert -disable *fv_checker.no_ready_when_full_a*

# If assertion bound - pre-condition reachable cycle >= 2:
# it's marked as "bounded_proven (auto) instead of "undetermined"
# this only affects the status report, not the proof
set_prove_inferred_target_bound on
# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
