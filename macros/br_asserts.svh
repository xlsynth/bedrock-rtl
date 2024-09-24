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

// Common macros for instantiating SystemVerilog Assertions (SVA).
// They help make code easier to write, read, and maintain by hiding
// the property boilerplate.
//
// The SystemVerilog language lacks native support for namespacing.
// Therefore we namespace all macros with the BR_ prefix (stands for Bedrock).

////////////////////////////////////////////////////////////////////////////////
// Static (elaboration-time) assertion macros
////////////////////////////////////////////////////////////////////////////////

`define BR_ASSERT_STATIC(__name__, __expr__) \
`ifdef SV_ASSERT_ON \
if (!(__expr__)) begin : gen__``__name__ \
__STATIC_ASSERT_FAILED__ __name__ (); \
end \
`endif

////////////////////////////////////////////////////////////////////////////////
// Concurrent assertion macros (evaluated on posedge of a clock and disabled during a reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`define BR_ASSERT(__name__, __expr__) \
`ifdef SV_ASSERT_ON \
__name__ : assert property (@(posedge clk) disable iff (rst) (__expr__)); \
`endif

// More expressive form of BR_ASSERT that allows the use of custom clock and reset signal names.
`define BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
`ifdef SV_ASSERT_ON \
__name__ : assert property (@(posedge __clk__) disable iff (__rst__) (__expr__)); \
`endif

////////////////////////////////////////////////////////////////////////////////
// Combinational assertion macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`define BR_ASSERT_COMB(__name__, __expr__) \
`ifdef SV_ASSERT_ON \
generate : __name__ \
always_comb begin \
assert property (__expr__); \
end \
endgenerate \
`endif

////////////////////////////////////////////////////////////////////////////////
// Concurrent cover macros (evaluated on posedge of a clock and disabled during a reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`define BR_COVER(__name__, __expr__) \
`ifdef SV_ASSERT_ON \
__name__ : cover property (@(posedge clk) disable iff (rst) (__expr__)); \
`endif

// More expressive form of BR_COVER that allows the use of custom clock and reset signal names.
`define BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
`ifdef SV_ASSERT_ON \
__name__ : cover property (@(posedge __clk__) disable iff (__rst__) (__expr__)); \
`endif

////////////////////////////////////////////////////////////////////////////////
// Combinational cover macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`define BR_COVER_COMB(__name__, __expr__) \
`ifdef SV_ASSERT_ON \
generate : __name__ \
always_comb begin \
cover property (__expr__); \
end \
endgenerate \
`endif

`endif // BR_ASSERTS_SVH
