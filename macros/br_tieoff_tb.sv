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

// Unit test for br_tieoff.svh macros

`include "br_tieoff.svh"

module br_tieoff_tb ();  // ri lint_check_waive NO_OUTPUT

  wire [1:0] foo = 2'b01;  // ri lint_check_waive CONST_ASSIGN
  wire bar = foo[0];  // ri lint_check_waive CONST_ASSIGN

  logic [1:0] zero;
  logic [1:0] one;
  logic [1:0] todo_zero;
  logic [1:0] todo_one;

  `BR_TIEOFF_ZERO(zero)
  `BR_TIEOFF_ONE(one)
  `BR_TIEOFF_ZERO_TODO(mgottscho, todo_zero)
  `BR_TIEOFF_ONE_TODO(mgottscho, todo_one)

endmodule : br_tieoff_tb
