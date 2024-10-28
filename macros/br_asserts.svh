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

`ifndef BR_ASSERTS_SVH
`define BR_ASSERTS_SVH

// ri lint_check_off LINE_LENGTH
// verilog_lint: waive-start line-length
// verilog_format: off

// Common macros for instantiating SystemVerilog Assertions (SVA).
// They help make code easier to write, read, and maintain by hiding
// the property boilerplate.
//
// The SystemVerilog language lacks native support for namespacing.
// Therefore we namespace all macros with the BR_ prefix (stands for Bedrock).

////////////////////////////////////////////////////////////////////////////////
// Static (elaboration-time) assertion macros
////////////////////////////////////////////////////////////////////////////////

`define BR_NOOP

`ifdef BR_ASSERT_ON
`define BR_ASSERT_STATIC(__name__, __expr__) \
if (!(__expr__)) begin : gen__``__name__ \
__STATIC_ASSERT_FAILED__ __STATIC_ASSERT_FAILED__``__name__ (); \
end
`else  // BR_ASSERT_ON
`define BR_ASSERT_STATIC(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

`define BR_ASSERT_STATIC_IN_PACKAGE(__name__, __expr__) \
typedef enum logic [1:0] { \
    __STATIC_ASSERT_OK__``__name__ = ((__expr__) ? 1 : 0), \
    __STATIC_ASSERT_FAILED__``__name__ = 0 \
} __static_assert_enum__``__name__;

////////////////////////////////////////////////////////////////////////////////
// Concurrent assertion macros (evaluated on posedge of a clock and disabled during a reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_ASSERT_ON
`define BR_ASSERT(__name__, __expr__) \
__name__ : assert property (@(posedge clk) disable iff (rst) (__expr__));
`else  // BR_ASSERT_ON
`define BR_ASSERT(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

// More expressive form of BR_ASSERT that allows the use of custom clock and reset signal names.
`ifdef BR_ASSERT_ON
`define BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
__name__ : assert property (@(posedge __clk__) disable iff (__rst__) (__expr__));
`else  // BR_ASSERT_ON
`define BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

////////////////////////////////////////////////////////////////////////////////
// Combinational assertion macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`ifdef BR_ASSERT_ON
`define BR_ASSERT_COMB(__name__, __expr__) \
always_comb begin  : gen_``__name__ \
assert (__expr__); \
end
`else  // BR_ASSERT_ON
`define BR_ASSERT_COMB(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

////////////////////////////////////////////////////////////////////////////////
// Concurrent cover macros (evaluated on posedge of a clock and disabled during a reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_COVER_ON
`define BR_COVER(__name__, __expr__) \
__name__ : cover property (@(posedge clk) disable iff (rst) (__expr__));
`else  // BR_COVER_ON
`define BR_COVER(__name__, __expr__) \
`BR_NOOP
`endif  // BR_COVER_ON

// More expressive form of BR_COVER that allows the use of custom clock and reset signal names.
`ifdef BR_COVER_ON
`define BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
__name__ : cover property (@(posedge __clk__) disable iff (__rst__) (__expr__));
`else  // BR_COVER_ON
`define BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_COVER_ON

////////////////////////////////////////////////////////////////////////////////
// Combinational cover macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`ifdef BR_COVER_ON
`define BR_COVER_COMB(__name__, __expr__) \
always_comb begin  : gen_``__name__ \
cover (__expr__); \
end
`else  // BR_COVER_ON
`define BR_COVER_COMB(__name__, __expr__) \
`BR_NOOP
`endif  // BR_COVER_ON

// verilog_format: on
// verilog_lint: waive-stop line-length
// ri lint_check_on LINE_LENGTH

`endif  // BR_ASSERTS_SVH
