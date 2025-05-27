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

# These should be assumptions because signals are primary inputs
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4.genStableChksRDInf.genRStableChks.slave_r_rdata_stable
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4_lite.genPropChksWRInf.genNoWrDatTblOverflow.genMas.master_w_wr_tbl_no_overflow

# TODO: disable covers to make nightly clean
cover -disable *

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
