// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef BR_UNUSED_SVH
`define BR_UNUSED_SVH

// ri lint_check_off LINE_LENGTH
// verilog_lint: waive-start line-length
// verilog_format: off

`define BR_UNUSED(__name__, __x__) br_misc_unused #(.BitWidth($bits(__x__))) br_misc_unused_``__name__(.in(__x__));

// ri lint_check_on LINE_LENGTH
// verilog_lint: waive-stop line-length
// verilog_format: on

`endif  // BR_UNUSED_SVH
