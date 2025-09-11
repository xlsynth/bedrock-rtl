# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

array set param_list [get_design_info -list parameter]
set SingleBeat $param_list(SingleBeat)

# disable AXI ABVIP covers
# ABVIP Max_pending default is 2, if overwritten to 1, those covers are reachable (then bunch of other covers are unreachable).
# TODO(bgelb): please double check, RTL probably has no back pressure
cover -disable *genPropChksRDInf.genNoRdTblOverflow.master_ar_rd_tbl_no_overflow:precondition1
cover -disable *genPropChksRDInf.genNoRdTblOverflow.genSlv.slave_ar_rd_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrTblOverflow.master_aw_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrTblOverflow.genSlv.slave_aw_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrDatTblOverflow.master_w_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrDatTblOverflow.genSlv.slave_w_wr_tbl_no_overflow:precondition1
if {$SingleBeat eq "1'b1"} {
  # these covers require multi-burst
  cover -disable *genPropChksRDInf.genAXI4Full.genChkMaxLen.genBurstWrap.master_ar_araddr_wrap_aligned:precondition1
  cover -disable *genPropChksRDInf.genAXI4Full.genChkMaxLen.genBurstWrap.master_ar_araddr_wrap_arlen:precondition1
  cover -disable *genPropChksWRInf.genAXI4Full.genChkMaxlenGr1.genBurstWrap.master_aw_awaddr_wrap_aligned:precondition1
  cover -disable *genPropChksWRInf.genAXI4Full.genChkMaxlenGr1.genBurstWrap.master_aw_awaddr_wrap_awlen:precondition1
  cover -disable *genPropChksWRInf.genAXI4Full.genDbcAw.genAwlenMaxLenGr1.genAwlenDatAcpt.master_aw_w_awlen_exact_len_dbc:precondition4
  cover -disable *genPropChksWRInf.genAXI4Full.genAwlenMaxLenGr1.genAwlenDatAcpt.master_aw_w_awlen_exact_len_collision_dbc_data_end:precondition1
  cover -disable *genPropChksWRInf.genAXI4Full.genAwlenMaxLenGr1.genAwlenDatAcpt.genChkDBC.master_aw_w_awlen_exact_len_collision_dbc_data_cont:precondition1
  cover -disable *genPropChksWRInf.genDbcW.genAXI4Full.genWlastExactLenDbc.master_w_aw_wlast_exact_len_dbc:precondition1
  cover -disable *genPropChksWRInf.genNoLite.genWlastCol.master_w_aw_wlast_exact_len_collision:precondition1
}

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
