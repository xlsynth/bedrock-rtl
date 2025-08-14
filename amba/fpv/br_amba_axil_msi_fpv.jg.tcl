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

# aw/w valid won't backpressure
assert -disable <embedded>::br_amba_axil_msi.monitor.axi.genPropChksWRInf.genNoWrTblOverflow.genMas.master_aw_wr_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_msi.monitor.axi.genPropChksWRInf.genNoWrDatTblOverflow.genMas.master_w_wr_tbl_no_overflow

# slave_ar_no_arvalid_arready_eventually : assume property (
#     disable iff (!aresetn||(rd_tbl_full && !rd_tbl_pop_ready))
#     `STRENGTH(##[0:$] arready))
# else $display ("%0t: Slave should not wait for arvalid to assert arready; ARM IHI 0022F: None",$time);

# above assumption is over-constraining FV TB, so jasper special cover :live is unreachable
# this means: It is impossible to satisfy all fairness constraints infinitely often.
assume -disable <embedded>::br_amba_axil_msi.monitor.axi.genPropChksRDInf.genSlaveLiveAR.slave_ar_no_arvalid_arready_eventually

# TODO(masai, bgelb): disable covers to make nightly clean
cover -disable *

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
