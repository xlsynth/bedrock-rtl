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
//
// Assertion macros are only enabled when BR_ASSERT_ON is defined.

////////////////////////////////////////////////////////////////////////////////
// Static (elaboration-time) assertion macros
////////////////////////////////////////////////////////////////////////////////

`define BR_NOOP

`ifdef BR_ASSERT_ON
`define BR_ASSERT_STATIC(__name__, __expr__) \
if (!(__expr__)) begin : gen__``__name__ \
__STATIC_ASSERT_FAILED__``__name__ __STATIC_ASSERT_FAILED__``__name__ (); \
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
// Concurrent assertion macros (evaluated on posedge of a clock and disabled during a synchronous active-high reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_ASSERT_ON
`define BR_ASSERT(__name__, __expr__) \
__name__ : assert property (@(posedge clk) disable iff (rst === 1'b1 || rst === 1'bx) (__expr__));
`else  // BR_ASSERT_ON
`define BR_ASSERT(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

// More expressive form of BR_ASSERT that allows the use of custom clock and reset signal names.
`ifdef BR_ASSERT_ON
`define BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
__name__ : assert property (@(posedge __clk__) disable iff (__rst__ === 1'b1 || __rst__ === 1'bx) (__expr__));
`else  // BR_ASSERT_ON
`define BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

////////////////////////////////////////////////////////////////////////////////
// Combinational assertion macros (evaluated continuously based on the expression sensitivity).
// Also pass if the expression is unknown.
////////////////////////////////////////////////////////////////////////////////

// BR_ASSERT_COMB is guarded with BR_ENABLE_ASSERT_COMB because some tools don't like immediate assertions,
// and/or $isunknown in combinational blocks, even when it's used inside of an assert statement.
`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_ASSERT_COMB
`define BR_ASSERT_COMB(__name__, __expr__) \
always_comb begin  : gen_``__name__ \
assert ($isunknown(__expr__) || (__expr__)); \
end
`else  // BR_ENABLE_COMB_CHECKS
`define BR_ASSERT_COMB(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_COMB_CHECKS
`else  // BR_ASSERT_ON
`define BR_ASSERT_COMB(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

////////////////////////////////////////////////////////////////////////////////
// Concurrent cover macros (evaluated on posedge of a clock and disabled during a synchronous active-high reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_ASSERT_ON
`define BR_COVER(__name__, __expr__) \
__name__ : cover property (@(posedge clk) disable iff (rst === 1'b1 || rst === 1'bx) (__expr__));
`else  // BR_ASSERT_ON
`define BR_COVER(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

// More expressive form of BR_COVER that allows the use of custom clock and reset signal names.
`ifdef BR_ASSERT_ON
`define BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
__name__ : cover property (@(posedge __clk__) disable iff (__rst__ === 1'b1 || __rst__ === 1'bx) (__expr__));
`else  // BR_ASSERT_ON
`define BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

////////////////////////////////////////////////////////////////////////////////
// Combinational cover macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`ifdef BR_ASSERT_ON
`define BR_COVER_COMB(__name__, __expr__) \
always_comb begin  : gen_``__name__ \
cover (__expr__); \
end
`else  // BR_ASSERT_ON
`define BR_COVER_COMB(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

////////////////////////////////////////////////////////////////////////////////
// Concurrent assumption macros (evaluated on posedge of a clock and disabled during a synchronous active-high reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_ASSERT_ON
`define BR_ASSUME(__name__, __expr__) \
__name__ : assume property (@(posedge clk) disable iff (rst === 1'b1 || rst === 1'bx) (__expr__));
`else  // BR_ASSERT_ON
`define BR_ASSUME(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ASSERT_ON

// More expressive form of BR_ASSUME that allows the use of custom clock and reset signal names.
`ifdef BR_ASSERT_ON
`define BR_ASSUME_CR(__name__, __expr__, __clk__, __rst__) \
__name__ : assume property (@(posedge __clk__) disable iff (__rst__ === 1'b1 || __rst__ === 1'bx) (__expr__));
`else  // BR_ASSERT_ON
`define BR_ASSUME_CR(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ASSERT_ON


// verilog_format: on
// verilog_lint: waive-stop line-length
// ri lint_check_on LINE_LENGTH

`endif  // BR_ASSERTS_SVH
