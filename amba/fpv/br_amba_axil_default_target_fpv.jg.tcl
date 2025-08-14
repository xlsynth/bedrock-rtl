# Copyright 2025 The Bedrock-RTL Authors
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

# disable AXI ABVIP cover properties
# ABVIP Max_pending default is 2, if overwritten to 1, those covers are reachable (then bunch of other covers are unreachable).
# TODO(bgelb): please double check, RTL probably has no back pressure
cover -disable *genPropChksRDInf.genNoRdTblOverflow.master_ar_rd_tbl_no_overflow:precondition1
cover -disable *genPropChksRDInf.genNoRdTblOverflow.genSlv.slave_ar_rd_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrTblOverflow.master_aw_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrTblOverflow.genSlv.slave_aw_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrDatTblOverflow.master_w_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrDatTblOverflow.genSlv.slave_w_wr_tbl_no_overflow:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
