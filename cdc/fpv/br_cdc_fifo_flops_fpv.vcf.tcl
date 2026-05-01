# Copyright 2024-2025 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Need this set up before analyze/elaborate
fv_quickstart
set_fml_var fml_coi_reduction false
set_fml_var fml_max_time 600s

# clock/reset set up
create_clock clk -period 10
create_random_clock -clock push_clk -period 10
create_random_clock -clock pop_clk -period 10
# Synopsys AE claims:
# create_random_clock is implemented by driving clock through a clock gater with enable being x
# therefore, user needs to add liveness assumptions to ensure clock will eventually toggle
fvassume push_clk_live -expr {!push_clk |-> s_eventually $rose(push_clk)} -clock clk
fvassume pop_clk_live -expr {!pop_clk |-> s_eventually $rose(pop_clk)} -clock clk

#set_grid_usage -type lsf=72 -control { bsub -app batch_normal -R "rusage[mem=32G]" }

# push/pop side primary input signals only toggle w.r.t its clock
set_change_at -internal -clock push_clk -posedge {push_valid push_data push_rst}
set_change_at -internal -clock pop_clk -posedge {pop_ready pop_rst}

# Assumptions mirrored from Jasper Tcl
fvassume delay_rst -expr {rst} -clock clk -depth 1
fvassume deassert_rst -expr {##1 !rst} -clock clk
fvassume env_assume_1 -expr {rst |-> push_rst} -clock clk
fvassume env_assume_2 -expr {rst |-> pop_rst} -clock clk
fvassume env_assume_3 -expr {!push_rst |=> !push_rst} -clock clk
fvassume env_assume_4 -expr {!pop_rst |=> !pop_rst} -clock clk
fvassume env_assume_5 -expr {s_eventually !push_rst} -clock clk
fvassume env_assume_6 -expr {s_eventually !pop_rst} -clock clk

# primary input control signal should be legal during reset
fvassume no_push_valid_during_reset -expr {push_rst |-> push_valid == 'd0} -clock push_clk

# overlap_cycles is not initialized, so it becomes a random value in FV.
# add assumption to force it to zero during first system_clock cycle.
fvassume push_overlap_cycles_init -expr {dut.br_cdc_fifo_ctrl_1r1w.br_cdc_fifo_ctrl_push_1r1w.br_cdc_fifo_push_ctrl.br_cdc_fifo_push_flag_mgr.br_cdc_fifo_reset_overlap_checks.overlap_cycles == 'd0} -clock clk -depth 1
fvassume pop_overlap_cycles_init -expr {dut.br_cdc_fifo_ctrl_1r1w.br_cdc_fifo_ctrl_pop_1r1w_inst.br_cdc_fifo_pop_ctrl.br_cdc_fifo_pop_flag_mgr.br_cdc_fifo_reset_overlap_checks.overlap_cycles == 'd0} -clock clk -depth 1

# push_count_gray is not initialized, so it becomes a random value in FV.
# When pop_rst falls, constrain the first push-count bit entering the pop-side
# CDC synchronizer to start at zero.
fvassume push_count_gray_init -expr {$fell(pop_rst) |-> dut.br_cdc_fifo_ctrl_1r1w.br_cdc_fifo_ctrl_pop_1r1w_inst.br_cdc_fifo_gray_count_sync_push2pop.gen_cdc_sync[0].br_cdc_bit_toggle_inst.br_gate_cdc_sync.in_d == 'd0} -clock pop_clk

report_fv_complexity

#run properties
check_fv -block
