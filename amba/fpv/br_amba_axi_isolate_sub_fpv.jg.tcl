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

# TODO: disable covers to make nightly clean
cover -disable *

# during isolate_req & !isolate_done window, downstream assertions don't matter
# Coded same assertion with precondition: isolate_req & !isolate_done in br_amba_axi_isolate_sub_fpv.sv
assert -disable {*downstream.genStableChksRDInf.genARStableChks.master_ar_arvalid_stable}
assert -disable {*downstream.genStableChksWRInf.genAWStableChks.master_aw_awvalid_stable}
assert -disable {*downstream.genStableChksWRInf.genWStableChks.master_w_wvalid_stable}

# aw/wready won't backpressure when DUT reaches maxOutstanding requests
assert -disable {*upstream.genPropChksWRInf.genNoWrTblOverflow.genSlv.slave_aw_wr_tbl_no_overflow}
assert -disable {*upstream.genPropChksWRInf.genNoWrDatTblOverflow.genSlv.slave_w_wr_tbl_no_overflow}

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
