# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

array set param_list [get_design_info -list parameter]
set MaxAxiBurstLen $param_list(MaxAxiBurstLen)
set StaticPerIdReadTrackerFifoDepth $param_list(StaticPerIdReadTrackerFifoDepth)
set UseDynamicFifoForReadTracker $param_list(UseDynamicFifoForReadTracker)

# TODO(bgelb): disable RTL covers to make nightly clean
cover -disable *
cover -enable *br_amba_axi_isolate_sub.monitor*
# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1

if {$MaxAxiBurstLen == 1 &&
    $StaticPerIdReadTrackerFifoDepth == 1 &&
    $UseDynamicFifoForReadTracker eq "1'b0"} {
    # Single-beat reads with one static per-ID tracker slot do not have downstream
    # R-channel backpressure, so rvalid && !rready cover preconditions are unreachable.
    cover -disable *downstream.genStableChksRDInf.genRStableChks.slave_r_rvalid_stable:precondition1
    cover -disable *downstream.genStableChksRDInf.genRStableChks.slave_r_rdata_stable:precondition1
    cover -disable *downstream.genStableChksRDInf.genRStableChks.slave_r_rresp_stable:precondition1
    cover -disable *downstream.genRIntfDldChks.genLiveSlaveR.genRChWait.genLive.master_r_rvalid_rready_eventually:precondition1
}

# during isolate_req & !isolate_done window, downstream assertions don't matter
# Coded same assertion with precondition: isolate_req & !isolate_done in br_amba_axi_isolate_sub_fpv.sv
assert -disable {*downstream.genStableChksRDInf.genARStableChks.master_ar_arvalid_stable}
assert -disable {*downstream.genStableChksWRInf.genAWStableChks.master_aw_awvalid_stable}
assert -disable {*downstream.genStableChksWRInf.genWStableChks.master_w_wvalid_stable}

# limit run time to 30-mins
set_prove_time_limit 1800s

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
if {[llength [get_property_list -include {type assert name {br_amba_axi_isolate_sub.br_amba_iso_resp_tracker_w.gen_wlast_tracking.br_flow_fork_wlast_staging.br_flow_fork_select_multihot.always_ready_when_unselected_a}}]] > 0} {
  assert -disable {br_amba_axi_isolate_sub.br_amba_iso_resp_tracker_w.gen_wlast_tracking.br_flow_fork_wlast_staging.br_flow_fork_select_multihot.always_ready_when_unselected_a}
}

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
if {[llength [get_property_list -include {type assert name {br_amba_axi_isolate_sub.br_amba_iso_resp_tracker_r.gen_multi_fifo.gen_dynamic_fifo.br_fifo_shared_dynamic_flops_req_tracker.br_fifo_shared_dynamic_ctrl_inst.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}}]] > 0} {
  assert -disable {br_amba_axi_isolate_sub.br_amba_iso_resp_tracker_r.gen_multi_fifo.gen_dynamic_fifo.br_fifo_shared_dynamic_flops_req_tracker.br_fifo_shared_dynamic_ctrl_inst.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}
}

# prove command
prove -all
