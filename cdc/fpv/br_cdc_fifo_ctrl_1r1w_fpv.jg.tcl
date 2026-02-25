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
#assume -env {!push_rst |=> !push_rst}
#assume -env {!pop_rst |=> !pop_rst}
assume -env {s_eventually !push_rst}
assume -env {s_eventually !pop_rst}

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

# overlap_cycles is not initialized, so it becomes a random value in FV.
# add assumption to force it to zero during first system_clock cycle.
assume -bound 1 {dut.br_cdc_fifo_ctrl_push_1r1w.br_cdc_fifo_push_ctrl.br_cdc_fifo_push_flag_mgr.br_cdc_fifo_reset_overlap_checks.overlap_cycles == 'd0}
assume -bound 1 {dut.br_cdc_fifo_ctrl_pop_1r1w_inst.br_cdc_fifo_pop_ctrl.br_cdc_fifo_pop_flag_mgr.br_cdc_fifo_reset_overlap_checks.overlap_cycles == 'd0}

# primary output control signal should be legal during reset
#assert -name fv_rst_check_push_ram_write_valid {@(posedge push_clk) \
#push_rst |-> push_ram_wr_valid == 'd0}
#
#assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
#pop_rst |-> pop_valid == 'd0}
#
#assert -name fv_rst_check_pop_ram_rd_addr_valid {@(posedge pop_clk) \
#pop_rst |-> pop_ram_rd_addr_valid == 'd0}

# push_count_gray is not initialized, so it becomes a random value in FV.
# It needs RamWriteLatency of push_clk cycles to be initialized to zero.
# Since push_clk : pop_clk ratio can be 10:1 in current set up, instead of waiting for 10xRamWriteLatency cycles,
# we just directly assume it to be zero at beginning.
array set param_list [get_design_info -instance fv_checker -list parameter]
set RamWriteLatency $param_list(RamWriteLatency)
for {set i 0} {$i < $RamWriteLatency} {incr i} {
  assume -bound 1 "dut.br_cdc_fifo_ctrl_push_1r1w.br_cdc_fifo_push_ctrl.br_cdc_fifo_push_flag_mgr.br_delay_nr_push_count_gray.stages\[$i\] == 'd0"
}

# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
