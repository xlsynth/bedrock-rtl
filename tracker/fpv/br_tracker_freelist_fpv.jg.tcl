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

# when alloc_valid is back pressured, it can not change next cycle
cover -disable {*gen_single_alloc_port.*_unstable_c}
cover -disable {*gen_multi_alloc_ports.*_instability_c}
# TODO: disable covers for now
cover -disable {br_tracker_freelist.br_enc_priority_encoder_free_entries*}

# prove command
prove -all
