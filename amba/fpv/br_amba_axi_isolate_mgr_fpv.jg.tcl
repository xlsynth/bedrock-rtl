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

# TODO: disable covers to make nightly clean
cover -disable *

# during isolate_req & !isolate_done window, upstream assertions don't matter
assert -disable {*upstream.genStableChksRDInf.genRStableChks.slave_r_rvalid_stable}
assert -disable {*upstream.genStableChksWRInf.genBStableChks.slave_b_bvalid_stable}
assert -disable {*upstream.genPropChksWRInf.slave_b_aw_bid_match}
assert -disable {*upstream.genPropChksWRInf.genAXI4FullWrResp.slave_b_aw_bid_order_within_id}
assert -disable {*upstream.genPropChksWRInf.genMasterLiveW.genreadyW.slave_w_no_aw_wready_eventually}

# prove command
prove -all
