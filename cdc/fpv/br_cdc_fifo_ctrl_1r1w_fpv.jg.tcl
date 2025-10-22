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

# limit run time to 10-mins
set_prove_time_limit 10m

prove -all
