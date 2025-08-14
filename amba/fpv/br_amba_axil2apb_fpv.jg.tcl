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

# TODO(bgelb): disable RTL unreachable cover
# This cover is unreachable because enable_priority_update is tired to 0 in RTL
cover -disable <embedded>::br_amba_axil2apb.br_arb_rr.br_arb_rr_internal.rr_state_internal.grant_onehot_A:precondition1

# prove command
prove -all
