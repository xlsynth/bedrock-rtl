// Copyright 2024-2025 The Bedrock-RTL Authors
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

// Not using br_misc_unread in this testbench to keep it isolated to covering tieoffs.
module br_tieoff_tb ();  // ri lint_check_waive NO_OUTPUT

  logic [1:0] zero;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic [1:0] one;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ

  `BR_TIEOFF_ZERO(zero)
  `BR_TIEOFF_ONE(one)

  logic [1:0] foo_zero;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic bar_zero;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic [1:0] foo_one;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic bar_one;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ

  `BR_TIEOFF_ZERO_NAMED(foobar, {foo_zero, bar_zero})
  `BR_TIEOFF_ONE_NAMED(foobar, {foo_one, bar_one})

  logic [1:0] baz_zero;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic qux_zero;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic [1:0] baz_one;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic qux_one;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ

  `BR_TIEOFF_ZERO_TODO(bazqux_temp, {baz_zero, qux_zero})
  `BR_TIEOFF_ONE_TODO(bazqux_temp, {baz_one, qux_one})

endmodule : br_tieoff_tb
