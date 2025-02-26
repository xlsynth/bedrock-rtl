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

# no ecc error: encoder and decoder are directly connected
task -create no_error -copy_all -source_task <embedded>
cover -disable {no_error::br_ecc_sed_fpv_monitor.br_ecc_sed_decoder.due_c}
assert -disable {no_error::br_ecc_sed_fpv_monitor.ecc_error*}
cover -disable {no_error::br_ecc_sed_fpv_monitor.ecc_error*}
prove -task {no_error}

# ecc error into decoder:
task -create ecc_error -copy_all -source_task <embedded>
task -set ecc_error
stopat enc_codeword
assert -disable {ecc_error::br_ecc_sed_fpv_monitor.*data_integrity_a}
prove -task {ecc_error}
