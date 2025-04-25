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
create_clock wr_clk -period 100
create_clock rd_clk -period 100

create_reset wr_rst -high
create_reset rd_rst -high

#design infomation
report_fv_complexity

#reset simulation
sim_run -stable
sim_save_reset

#run properties
check_fv -block
report_fv -list
