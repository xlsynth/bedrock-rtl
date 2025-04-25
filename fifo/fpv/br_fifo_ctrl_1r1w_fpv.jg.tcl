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

# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_wr_valid {rst |-> ram_wr_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {rst |-> ram_rd_addr_valid == 'd0}

# disable primary input side RTL integration assertion
# it's best practice to have valid/data stability when backpressured,
# but the FIFO itself doesn't care and will work fine even if it's unstable
assert -disable *br_fifo_push_ctrl.*valid_data_stable_when_backpressured_a

# TODO:
cover -disable *

# prove command
prove -all
