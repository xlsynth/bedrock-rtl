# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
clock push_clk -from 1 -to 10 -both_edges
clock pop_clk -from 1 -to 10 -both_edges

# declare always_in system clock
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 30 -name delay_rst {rst}
assume -name deassert_rst {##30 !rst}
# reset are ready at different times
assume -env {rst |-> push_rst}
assume -env {rst |-> pop_rst}
#assume -env {!push_rst |=> !push_rst}
#assume -env {!pop_rst |=> !pop_rst}
assume -env {s_eventually !push_rst}
assume -env {s_eventually !pop_rst}

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {push_rst \
            push_sender_in_reset \
            push_credit_stall \
            push_valid \
            push_data \
            credit_initial_push \
            credit_withhold_push} push_clk
clock -rate {pop_rst pop_ready} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> \
(credit_initial_push <= Depth) && $stable(credit_initial_push)}

assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> push_valid == 'd0}

# overlap_cycles is not initialized, so it becomes a random value in FV.
# add assumption to force it to zero during first system_clock cycle.
assume -bound 1 {dut.br_cdc_fifo_ctrl_1r1w_push_credit.br_cdc_fifo_ctrl_push_1r1w_push_credit_inst.br_cdc_fifo_push_ctrl_credit.br_cdc_fifo_push_flag_mgr.br_cdc_fifo_reset_overlap_checks.overlap_cycles == 'd0}
assume -bound 1 {dut.br_cdc_fifo_ctrl_1r1w_push_credit.br_cdc_fifo_ctrl_pop_1r1w_inst.br_cdc_fifo_pop_ctrl.br_cdc_fifo_pop_flag_mgr.br_cdc_fifo_reset_overlap_checks.overlap_cycles == 'd0}

# primary output control signal should be legal during reset
#assert -name fv_rst_check_push_credit {@(posedge push_clk) \
#push_rst | push_sender_in_reset |-> push_credit == 'd0}
#
#assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
#pop_rst |-> pop_valid == 'd0}

# disable cdc_fifo_basic_fpv_monitor assertions don't apply to DUT
# no push_ready signal in push credit interface
assert -disable *fv_checker.no_ready_when_full_a*

# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
