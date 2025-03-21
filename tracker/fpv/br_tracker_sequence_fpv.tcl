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

# counter inc and dec is always 1
# there is no reinit
cover -disable {*br_counter_incr_allocate_counter.plus_zero_a*}
cover -disable {*br_counter_incr_allocate_counter.reinit_no_incr_a*}
cover -disable {*br_counter_incr_allocate_counter.reinit_and_incr_c*}
cover -disable {*br_counter_free_entry_counter.increment_min_c*}
cover -disable {*br_counter_free_entry_counter.decrement_min_c*}
cover -disable {*br_counter_free_entry_counter.reinit_and_change_c*}

# prove command
prove -all
