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

# TODO(bgelb):
cover -disable *br_amba_axil2apb.br_arb_rr.no_update_same_grants_A:precondition1
cover -disable *br_amba_axil2apb.br_arb_rr.grant_without_state_update_c

# TODO(masai): ABVIP covers are fully encrypted, impossible to debug
# OK to disable for now since those dbc related covers are checking data before control
# I realize these covers are unreachable for AXI-Lite
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_addr2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_burst2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_size2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_len2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.master_w_aw_wstrb_valid_non_dbc:precondition1


# prove command
prove -all
