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
create_clock clk -period 100
create_reset rst -high
#design infomation
report_fv_complexity

# standard use case: request will hold until grant
fvtask -create standard -copy FPV

# non-standard use case: request will NOT hold until grant
fvtask -create special -copy FPV
fvdisable {special::*req_hold_until_grant_a}
fvdisable {special::*no_deadlock_a}

#run properties
fvtask standard
check_fv -block
report_fv

fvtask special
check_fv -block
