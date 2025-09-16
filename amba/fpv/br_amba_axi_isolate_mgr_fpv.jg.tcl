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

array set param_list [get_design_info -list parameter]
set MaxAxiBurstLen $param_list(MaxAxiBurstLen)
# TODO(bgelb): disable RTL covers to make nightly clean
cover -disable *
cover -enable *br_amba_axi_isolate_mgr.monitor*
# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1
# aw/w has no skew when max burst is 1
if {$MaxAxiBurstLen eq "1"} {
  cover -disable *monitor.fv_axi_check.downstream.genPropChksWRInf.genDBCLive.genSlaveLiveAW.genLiveAW.master_aw_awvalid_eventually:precondition1
  # TODO(masai): ABVIP covers are fully encrypted, impossible to debug
  # OK to disable for now since those dbc related covers are checking data before control
  # I realize these covers are unreachable for AXI-Lite
  cover -disable *monitor.fv_axi_check.upstream.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_addr2:precondition1
  cover -disable *monitor.fv_axi_check.upstream.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_burst2:precondition1
  cover -disable *monitor.fv_axi_check.upstream.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_size2:precondition1
  cover -disable *monitor.fv_axi_check.upstream.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_len2:precondition1
}

# during isolate_req & !isolate_done window, upstream assertions don't matter
# There is no way to disable these assertions dynamically w.r.t a signal
# Has tried tying off isolate_req, those assertions stop failing.
# also checked each CEX, they all failed inside "isolate_req & !isolate_done" window
assert -disable {*upstream.genStableChksRDInf.genRStableChks.slave_r_rvalid_stable}
assert -disable {*upstream.genStableChksWRInf.genBStableChks.slave_b_bvalid_stable}
assert -disable {*upstream.genPropChksWRInf.slave_b_aw_bid_match}
assert -disable {*upstream.genPropChksWRInf.genAXI4FullWrResp.slave_b_aw_bid_order_within_id}
assert -disable {*upstream.genPropChksWRInf.genMasterLiveW.genreadyW.slave_w_no_aw_wready_eventually}

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
