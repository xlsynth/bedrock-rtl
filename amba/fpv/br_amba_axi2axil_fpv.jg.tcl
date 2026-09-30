# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# These should be assumptions because signals are primary inputs
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4.genStableChksRDInf.genRStableChks.slave_r_rdata_stable
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4_lite.genPropChksWRInf.genNoWrDatTblOverflow.genMas.master_w_wr_tbl_no_overflow

# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1

# The monitor's request prediction FIFOs should never fill because the DUT
# backpressures AXI requests before accepting more split requests than it can
# track. Disable these helper assertion preconditions so the run does not fail
# on intentionally unreachable monitor-full states.
cover -disable *monitor.fv_aw_req_fifo.gen_Bypass_ast.no_push_full_a:precondition1
cover -disable *monitor.fv_ar_req_fifo.gen_Bypass_ast.no_push_full_a:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
if {[llength [get_property_list -include {type assert name {br_amba_axi2axil.br_amba_axi2axil_core_write.br_flow_fork_flow_reg_pop.br_flow_fork_select_multihot.always_ready_when_unselected_a}}]] > 0} {
  assert -disable {br_amba_axi2axil.br_amba_axi2axil_core_write.br_flow_fork_flow_reg_pop.br_flow_fork_select_multihot.always_ready_when_unselected_a}
}

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
if {[llength [get_property_list -include {type assert name {br_amba_axi2axil.br_amba_axi2axil_core_read.br_flow_fork_flow_reg_pop.br_flow_fork_select_multihot.always_ready_when_unselected_a}}]] > 0} {
  assert -disable {br_amba_axi2axil.br_amba_axi2axil_core_read.br_flow_fork_flow_reg_pop.br_flow_fork_select_multihot.always_ready_when_unselected_a}
}

# prove command
prove -all
