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

array set param_list [get_design_info -list parameter]
set SingleBeat $param_list(SingleBeat)
# TODO(bgelb): disable RTL unreachable covers
if {$SingleBeat == 0} {
  cover -disable *br_amba_axi_default_target.gen_multi_beat.br_counter_incr_arlen.gen_wrap_impl_check.value_overflow_a:precondition1
  cover -disable *br_amba_axi_default_target.gen_multi_beat.br_counter_incr_arlen.gen_wrap_impl_check.maxvalue_plus_one_a:precondition1
  cover -disable *br_amba_axi_default_target.gen_multi_beat.br_counter_incr_arlen.gen_cover_zero_increment.plus_zero_a:precondition1
  cover -disable *br_amba_axi_default_target.gen_multi_beat.br_counter_incr_arlen.gen_cover_reinit.gen_cover_reinit_no_incr.reinit_no_incr_a:precondition1
}

# disable AXI ABVIP covers
# ABVIP Max_pending default is 2, if overwritten to 1, those covers are reachable (then bunch of other covers are unreachable).
# TODO(bgelb): please double check, RTL probably has no back pressure
cover -disable *genPropChksRDInf.genNoRdTblOverflow.master_ar_rd_tbl_no_overflow:precondition1
cover -disable *genPropChksRDInf.genNoRdTblOverflow.genSlv.slave_ar_rd_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrTblOverflow.master_aw_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrTblOverflow.genSlv.slave_aw_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrDatTblOverflow.master_w_wr_tbl_no_overflow:precondition1
cover -disable *genPropChksWRInf.genNoWrDatTblOverflow.genSlv.slave_w_wr_tbl_no_overflow:precondition1
if {$SingleBeat == 1} {
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
