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
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

get_design_info

# primary input control signal should be legal during reset
assume -name initial_value_during_reset {rst | push_sender_in_reset |-> \
(credit_initial_push <= MaxCredit) && $stable(credit_initial_push)}
assume -name no_ram_rd_data_valid_during_reset {rst | push_sender_in_reset |-> ram_rd_data_valid == 'd0}
assume -name no_push_valid_during_reset {rst | push_sender_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_credit {rst | push_sender_in_reset |-> push_credit == 'd0}
assert -name fv_rst_check_pop_valid {rst | push_sender_in_reset |-> pop_valid == 'd0}

# The push_ready is tied to 1, so the precondition of the assumption won't be met
cover -disable *br_fifo_basic_fpv_monitor.gen_push_backpressure_assume.no_push_backpressure*

# limit run time to 10-mins
set_prove_time_limit 600s

# prove command
prove -all
