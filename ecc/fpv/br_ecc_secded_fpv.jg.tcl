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

# disable ecc error covers
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.due_no_h_column_match_a:precondition1}
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.error_correction_a:precondition1}
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.ce_c}
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.due_c}

# prove command
prove -all
