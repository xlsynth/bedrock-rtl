# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# Unreachable RTL implementation covers
cover -disable *br_flow_reg_both_write_*.br_flow_reg_rev.br_flow_checks_valid_data_impl.gen_backpressure_checks.gen_valid_stability_checks.gen_valid_data_stability_checks.gen_valid_data_stability_per_flow*.valid_data_stable_when_backpressured_a:precondition1

# disable ABVIP covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1
# If aw/w channels have skew, these covers will be reachable.
# That's why they are reachable for root.
# For downstream branch and trunk, only when both aw and w are present, downstream_valid will be generated.
cover -disable *trunk.genPropChksWRInf.genDBCLive.genSlaveLiveAW.genLiveAW.master_aw_awvalid_eventually:precondition1
cover -disable *trunk.genPropChksWRInf.genSlaveLiveW.genLiveW.master_w_wvalid_eventually:precondition1
cover -disable *branch.genPropChksWRInf.genDBCLive.genSlaveLiveAW.genLiveAW.master_aw_awvalid_eventually:precondition1
cover -disable *branch.genPropChksWRInf.genSlaveLiveW.genLiveW.master_w_wvalid_eventually:precondition1
# TODO(masai): ABVIP covers are fully encrypted, impossible to debug
# OK to disable for now since those dbc related covers are checking data before control
# I realize these covers are unreachable for AXI-Lite
cover -disable *monitor.root.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_addr2:precondition1
cover -disable *monitor.root.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_burst2:precondition1
cover -disable *monitor.root.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_size2:precondition1
cover -disable *monitor.root.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_len2:precondition1
cover -disable *monitor.root.genPropChksWRInf.genByStrb.master_w_aw_wstrb_valid_non_dbc:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
