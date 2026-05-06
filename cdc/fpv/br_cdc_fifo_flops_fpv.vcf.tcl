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

# Declare system reset
create_reset rst -sync -value high

# These reset-domain constraints must be in place before sim_run to affect
# reset-state computation. Normal temporal fvassume properties only apply
# after sim_save_reset.
fvassume env_assume_1 -env -expr {!rst || push_rst}
fvassume env_assume_2 -env -expr {!rst || pop_rst}
sim_force push_rst -apply 1'b1
sim_force pop_rst -apply 1'b1
sim_run -stable
sim_release push_rst
sim_release pop_rst
# push_rst and pop_rst can deassert any time in random order
fvassume env_assume_3 -expr {!push_rst |=> !push_rst} -clock clk
fvassume env_assume_4 -expr {!pop_rst |=> !pop_rst} -clock clk
fvassume env_assume_5 -expr {s_eventually !push_rst} -clock clk
fvassume env_assume_6 -expr {s_eventually !pop_rst} -clock clk

# unitialized flop will be initialized to 0
# Then we don't have to wait for long reset sequence before FV can start checking properties
sim_set_state -uninitialized -apply 0
sim_save_reset

# primary input control signal should be legal during reset
fvassume -env no_push_valid_during_reset -expr {push_rst |-> push_valid == 'd0} -clock push_clk

report_fv_complexity

#run properties
check_fv -block
