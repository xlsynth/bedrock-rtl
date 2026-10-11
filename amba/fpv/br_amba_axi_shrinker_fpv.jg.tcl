# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info
array set param_list [get_design_info -list parameter]

# limit run time to 30-mins
set_prove_time_limit 30m

# fv_fifo is a bit oversized
cover -disable *monitor.w_fifo.gen_Bypass_ast.no_push_full_a:precondition1

# br_flow_fork ties select to all ones, so the zero-select precondition is unreachable.
assert -disable {br_amba_axi_shrinker.br_flow_fork_aw.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# With unregistered wide responses, the read tracker and narrow R stage cannot
# fill the wide checker's oversized read table. Keep the overflow assumption;
# exclude only its unreachable full-table precondition.
if {$param_list(RegisterWideOutputs) eq "1'b0"} {
  cover -disable *monitor.wide.genPropChksRDInf.genNoRdTblOverflow.master_ar_rd_tbl_no_overflow:precondition1
}

# Without narrow output registers, write data follows its accepted address.
# These data-before-address and same-cycle address/data preconditions cannot
# occur in this mode. Keep the corresponding functional assertions enabled.
if {$param_list(RegisterNarrowOutputs) eq "1'b0"} {
  cover -disable *monitor.narrow.genPropChksWRInf.genAXI4Full.genAwlenMaxLenGr1.genAwlenDatAcpt.master_aw_w_awlen_exact_len_collision_dbc_data_end:precondition1
  cover -disable *monitor.narrow.genPropChksWRInf.genAXI4Full.genAwlenMaxLenGr1.genAwlenDatAcpt.genChkDBC.master_aw_w_awlen_exact_len_collision_dbc_data_cont:precondition1
  cover -disable *monitor.narrow.genPropChksWRInf.genNoLite.genWlastCol.master_w_aw_wlast_exact_len_collision:precondition1
  cover -disable *monitor.narrow.genPropChksWRInf.genWlastMaxlenGr1.master_w_aw_wlast_exact_len:precondition3
  cover -disable *monitor.narrow.genPropChksWRInf.genWlastMaxlenGr1.master_w_aw_wlast_exact_len:precondition4
  cover -disable *monitor.narrow.genPropChksWRInf.GenByStrbChk.master_w_aw_wstrb_valid_collision:precondition1
}

# prove command
prove -all
