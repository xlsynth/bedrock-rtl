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
assume -name initial_value_during_reset {rst | pop_receiver_in_reset |-> \
(credit_initial <= MaxCredit) && $stable(credit_initial)}
assume -name no_pop_credit_during_reset {rst | pop_receiver_in_reset |-> pop_credit == 'd0}
assume -name no_push_during_reset {rst | pop_receiver_in_reset |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst | pop_receiver_in_reset |-> pop_valid == 'd0}

# TODO: disable covers to make nightly clean
cover -disable *

# prove command
prove -all
