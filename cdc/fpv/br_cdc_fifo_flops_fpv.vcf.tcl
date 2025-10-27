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
# fv_quickstart
# set_fml_var fml_coi_reduction false
# set_app_var define_synthesis_macro false

# clock/reset set up
create_clock clk -period 10
#create_random_clock -clock push_clk -period 10
#create_random_clock -clock pop_clk -period 10
# create clock with ratio 3:5
create_clock push_clk -period 30
create_clock pop_clk -period 50
# Synopsys AE claims:
# create_random_clock is implemented by driving clock through a clock gater with enable being x
# therefore, user needs to add liveness assumptions to ensure clock will eventually toggle
fvassume push_clk_live -expr {!push_clk |-> s_eventually $rose(push_clk)} -clock clk
fvassume pop_clk_live -expr {!pop_clk |-> s_eventually $rose(pop_clk)} -clock clk

create_reset rst -value high
create_reset push_rst -value high
create_reset pop_rst -value high

#set_grid_usage -type lsf=72 -control { bsub -app batch_normal -R "rusage[mem=32G]" }

# push/pop side primary input signals only toggle w.r.t its clock
set_change_at -internal -clock push_clk -posedge {push_valid push_data}
set_change_at -internal -clock pop_clk -posedge {pop_ready}

#run properties
check_fv -block
