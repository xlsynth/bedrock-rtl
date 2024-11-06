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

// Unit test for br_unused.svh macros

`include "br_unused.svh"

module br_unused_tb ();  // ri lint_check_waive NO_OUTPUT

  wire [1:0] foo = 2'b01;  // ri lint_check_waive CONST_ASSIGN
  wire bar = foo[0];  // ri lint_check_waive CONST_ASSIGN

  `BR_UNUSED(bar)
  `BR_UNUSED_NAMED(foo1, foo[1])

endmodule : br_unused_tb
