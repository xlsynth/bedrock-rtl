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

`ifndef BR_TIEOFF_SVH
`define BR_TIEOFF_SVH

`define BR_TIEOFF_ZERO(__x__) \
/* ri lint_check_waive CONST_ASSIGN */ \
assign __x__ = {$bits(__x__){1'b0}};

`define BR_TIEOFF_ONE(__x__) \
/* ri lint_check_waive CONST_ASSIGN */ \
assign __x__ = {$bits(__x__){1'b1}};

`define BR_TIEOFF_ZERO_TODO(__name__, __x__) \
/* TODO(__name__): Implement logic for __x__ */ \
/* ri lint_check_waive CONST_ASSIGN */ \
assign __x__ = {$bits(__x__){1'b0}};

`define BR_TIEOFF_ONE_TODO(__name__, __x__) \
/* TODO(__name__): Implement logic for __x__ */ \
/* ri lint_check_waive CONST_ASSIGN */ \
assign __x__ = {$bits(__x__){1'b1}};

`endif  // BR_TIEOFF_SVH
