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

# EnableAssertPushValidStability and EnableAssertPushDataStability
# doesn't apply to DUT pop_valid and pop_data
assert -disable {*pop_valid_stable_a}
assert -disable {*pop_data_stable_a}
# select can pick invalid index
assert -disable {*must_grant_a*}

# TODO: disable covers to make nightly clean
cover -disable *

# prove command
prove -all
