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

proc create_random_clock {clk main_clk} {
  set clk_en ${clk}_en
  virtual_net $clk_en
  replace_driver $clk -expression "$main_clk && $clk_en" -env
  assume -reset $clk_en
  assume "s_eventually $clk_en"
}

# clock/reset set up
clock clk
# random clock experiment:
 create_random_clock push_clk clk
 create_random_clock pop_clk clk
# tot set up:
# clock push_clk -from 1 -to 10 -both_edges
# clock pop_clk -from 1 -to 10 -both_edges
# quick 3:5 ratio test
# clock push_clk -factor 3
# clock pop_clk -factor 5
reset rst push_rst pop_rst

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {push_valid push_data} push_clk
clock -rate {pop_ready} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
pop_rst |-> pop_valid == 'd0}

# If assertion bound - pre-condition reachable cycle >= 2:
# it's marked as "bounded_proven (auto) instead of "undetermined"
# this only affects the status report, not the proof
set_prove_inferred_target_bound on
# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
