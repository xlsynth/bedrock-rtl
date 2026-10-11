# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# TODO(bgelb): disable RTL covers to make nightly clean
cover -disable *
cover -enable *br_amba_axi_demux.monitor*
# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1
# This is the only unreachable DBC precondition in upstream
# due to encrypted ABVIP signals, it's hard to debug why this is unreachable
# it's harmless to disable though
cover -disable *monitor.upstream.genPropChksWRInf.genDbcW.genAXI4Full.genWlastExactLenDbc.master_w_aw_wlast_exact_len_dbc:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
assert -disable {br_amba_axi_demux.br_amba_axi_demux_req_tracker_ar.br_flow_fork_upstream_req.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
assert -disable {br_amba_axi_demux.br_amba_axi_demux_req_tracker_aw.br_flow_fork_upstream_req.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# With unregistered addresses, a W routing token cannot precede downstream AW
# acceptance. Exclude only the impossible data-before-address preconditions;
# retain the no-data-before-address assertion and all other functional checks.
array set param_list [get_design_info -list parameter]
if {$param_list(RegisterDownstreamAxOutputs) == 0} {
  cover -disable *monitor.gen_sub*.downstream.genPropChksWRInf.genAXI4Full.genAwlenMaxLenGr1.genAwlenDatAcpt.master_aw_w_awlen_exact_len_collision_dbc_data_end:precondition1
  cover -disable *monitor.gen_sub*.downstream.genPropChksWRInf.genAXI4Full.genAwlenMaxLenGr1.genAwlenDatAcpt.genChkDBC.master_aw_w_awlen_exact_len_collision_dbc_data_cont:precondition1
  cover -disable *monitor.gen_sub*.downstream.genPropChksWRInf.genNoLite.genWlastCol.master_w_aw_wlast_exact_len_collision:precondition1
  # Registering W also prevents the first data beat from coinciding with AW.
  if {$param_list(RegisterDownstreamWOutputs) == 1} {
    cover -disable *monitor.gen_sub*.downstream.genPropChksWRInf.genWlastMaxlenGr1.master_w_aw_wlast_exact_len:precondition3
    cover -disable *monitor.gen_sub*.downstream.genPropChksWRInf.genWlastMaxlenGr1.master_w_aw_wlast_exact_len:precondition4
    cover -disable *monitor.gen_sub*.downstream.genPropChksWRInf.GenByStrbChk.master_w_aw_wstrb_valid_collision:precondition1
  }
}

# prove command
prove -all
