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
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

# TODO: disable covers to make nightly clean
cover -disable *

# primary input control signal should be legal during reset
array set param_list [get_design_info -list parameter]
set NumFifos $param_list(NumFifos)
for {set i 0} {$i < $NumFifos} {incr i} {
  assume -name initial_value_during_reset_$i "\$stable(credit_initial_push\[$i\])"
}

# limit run time to 10-mins
set_prove_time_limit 600s

# prove command
prove -all
