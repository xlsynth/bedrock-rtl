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
clock wr_clk -from 1 -to 10 -both_edges
clock rd_clk -from 1 -to 10 -both_edges
reset rst wr_rst rd_rst

# wr/rd primary input signals only toggle w.r.t its clock
clock -rate {wr_rst \
            wr_valid \
            wr_addr \
            wr_data \
            wr_word_en} wr_clk
clock -rate {rd_rst \
            rd_addr_valid \
            rd_addr \
            rd_data_valid \
            rd_data} rd_clk

# prove command
prove -all
