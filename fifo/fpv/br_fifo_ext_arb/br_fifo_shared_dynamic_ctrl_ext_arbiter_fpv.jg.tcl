# Copyright 2025 The Bedrock-RTL Authors
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

# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}
assume -name no_data_ram_rd_data_valid {rst |-> data_ram_rd_data_valid == 'd0}
assume -name no_ptr_ram_rd_data_valid {rst |-> ptr_ram_rd_data_valid == 'd0}
array set param_list [get_design_info -list parameter]
set NumReadPorts $param_list(NumReadPorts)
for {set i 0} {$i < $NumReadPorts} {incr i} {
  assume -name grant_onehot_during_reset_$i "\$onehot0(arb_grant\[$i\])"
}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_wr_valid {rst |-> data_ram_wr_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {rst |-> data_ram_rd_addr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_wr_valid {rst |-> ptr_ram_wr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_rd_addr_valid {rst |-> ptr_ram_rd_addr_valid == 'd0}

# TODO: disable covers to make nightly clean
cover -disable *

# limit run time to 10-mins
set_prove_time_limit 600s

# prove command
prove -all
