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

# target ar/aw/w ready won't backpressure
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.target.genPropChksRDInf.genNoRdTblOverflow.genSlv.slave_ar_rd_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.target.genPropChksWRInf.genNoWrTblOverflow.genSlv.slave_aw_wr_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.target.genPropChksWRInf.genNoWrDatTblOverflow.genSlv.slave_w_wr_tbl_no_overflow

# prove command
prove -all
