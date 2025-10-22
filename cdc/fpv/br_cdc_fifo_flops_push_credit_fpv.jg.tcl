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
create_random_clock push_clk clk
create_random_clock pop_clk clk

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
clock -rate {pop_rst pop_ready} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> \
(credit_initial_push <= Depth) && $stable(credit_initial_push)}

assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_credit {@(posedge push_clk) \
push_rst | push_sender_in_reset |-> push_credit == 'd0}

assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
pop_rst |-> pop_valid == 'd0}

# disable cdc_fifo_basic_fpv_monitor assertions don't apply to DUT
# no push_ready signal in push credit interface
assert -disable *fv_checker.no_ready_when_full_a*

# limit run time to 10-mins
set_prove_time_limit 10m

prove -all
