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

# These should be assumptions because signals are primary inputs
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4.genStableChksRDInf.genRStableChks.slave_r_rdata_stable
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4_lite.genPropChksWRInf.genNoWrDatTblOverflow.genMas.master_w_wr_tbl_no_overflow

# TODO(bgelb): disable RTL unreachable covers
cover -disable *br_amba_axi2axil_core_write.br_counter_incr_req.gen_wrap_impl_check.value_overflow_a:precondition1
cover -disable *br_amba_axi2axil_core_write.br_counter_incr_req.gen_wrap_impl_check.maxvalue_plus_one_a:precondition1
cover -disable *br_amba_axi2axil_core_write.br_counter_incr_req.gen_cover_zero_increment.plus_zero_a:precondition1
cover -disable *br_amba_axi2axil_core_write.br_counter_incr_req.gen_cover_reinit.gen_cover_reinit_no_incr.reinit_no_incr_a:precondition1
cover -disable *br_amba_axi2axil_core_write.br_fifo_flops_resp_tracker.br_fifo_ctrl_1r1w.br_fifo_push_ctrl.br_fifo_push_ctrl_core.br_flow_checks_valid_data_intg.gen_flow_checks\[0\].gen_backpressure_checks.gen_valid_stability_checks.gen_valid_data_stability_checks.valid_data_stable_when_backpressured_a:precondition1
cover -disable *br_amba_axi2axil_core_read.br_counter_incr_req.gen_cover_zero_increment.plus_zero_a:precondition1
cover -disable *br_amba_axi2axil_core_read.br_counter_incr_req.gen_cover_reinit.gen_cover_reinit_no_incr.reinit_no_incr_a:precondition1
cover -disable *br_amba_axi2axil_core_read.br_fifo_flops_resp_tracker.br_fifo_ctrl_1r1w.br_fifo_push_ctrl.br_fifo_push_ctrl_core.br_flow_checks_valid_data_intg.gen_flow_checks\[0\].gen_backpressure_checks.gen_valid_stability_checks.gen_valid_data_stability_checks.valid_data_stable_when_backpressured_a:precondition1

# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
