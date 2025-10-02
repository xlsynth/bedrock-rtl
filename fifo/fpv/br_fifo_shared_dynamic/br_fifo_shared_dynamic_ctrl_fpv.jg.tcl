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

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_wr_valid {rst |-> data_ram_wr_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {rst |-> data_ram_rd_addr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_wr_valid {rst |-> ptr_ram_wr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_rd_addr_valid {rst |-> ptr_ram_rd_addr_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 600s

# The output of this flow fork will not be unstable because we constrain the
# ready to hold until valid is asserted.
# TODO(zhemao): Find a way to disable in RTL
cover -disable *br_flow_fork_head.br_flow_checks_valid_data_impl.*valid_unstable_c
# There are certain cases where the backpressure precondition on these checks are unreachable.
# Annoying to disable in RTL because only certain output ports are affected.
# These are redundant with the push integration checks on the muxes, so just disable them all
# TODO(masai): Figure out a more fine-grained waiver
array set param_list [get_design_info -list parameter]
set NumReadPorts $param_list(NumReadPorts)
set Depth $param_list(Depth)
if {$Depth < 2 * $NumReadPorts} {
  cover -disable *br_fifo_shared_read_xbar*br_flow_demux_select_unstable*br_flow_checks_valid_data_impl.*stable*
}

# prove command
prove -all
