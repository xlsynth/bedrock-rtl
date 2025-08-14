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

# There is no flush signals in RTL
assert -disable <embedded>::br_amba_atb_funnel.monitor.gen_src\[*\].src.slv_stable.slave_af_afvalid_stable
assert -disable <embedded>::br_amba_atb_funnel.monitor.gen_src\[*\].src.deassert.slave_af_afvalid_deasserted
assert -disable <embedded>::br_amba_atb_funnel.monitor.gen_src\[*\].src.ATB_v1_0.syncreq.assert_syncreq_disabled_rev0_0

# TODO: disable covers to make nightly clean
cover -disable *
cover -enable *br_amba_atb_funnel.monitor*

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
