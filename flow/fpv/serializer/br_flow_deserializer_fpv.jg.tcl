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

# TODO: Unreachable covers that need to be debugged
cover -disable {*gen_dr_gt_1.incomplete_pop_flit_a*}
cover -disable {*br_counter_incr_push_flit_id.gen_wrap_impl_check.value_overflow_a*}
cover -disable {*br_counter_incr_push_flit_id.gen_wrap_impl_check.maxvalue_plus_one_a*}
cover -disable {*br_counter_incr_push_flit_id.plus_zero_a*}
cover -disable {*br_counter_incr_push_flit_id.value_temp_oob_c*}
cover -disable {*br_counter_incr_push_flit_id.reinit_and_incr_c*}
cover -disable {*monitor.gen_ast[0].fv_pop_data_stable_a*}
cover -disable {*monitor.dont_care_c*}

# prove command
prove -all
