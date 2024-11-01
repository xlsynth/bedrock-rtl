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

`ifndef BR_GATES_SVH
`define BR_GATES_SVH

// Common macros for instantiating logic gates in a design.
// They help make RTL code easier to write, read, and maintain by hiding
// the implementation boilerplate for port definitions.
//
// The SystemVerilog language lacks native support for namespacing.
// Therefore we namespace all macros with the BR_ prefix (stands for Bedrock).

// verilog_format: off

// Buffer
`define BR_GATE_BUF(__iname__, __out__, __in__) \
br_gate_buf br_gate_buf_``__iname__`` ( \
    .in(__in__), \
    .out(__out__) \
)

// Clock Buffer
`define BR_GATE_CLK_BUF(__iname__, __out__, __in__) \
br_gate_clk_buf br_gate_clk_buf_``__iname__`` ( \
    .in(__in__), \
    .out(__out__) \
)

// Inverter
`define BR_GATE_INV(__iname__, __out__, __in__) \
br_gate_inv br_gate_inv_``__iname__`` ( \
    .in(__in__), \
    .out(__out__) \
)

// 2-Input AND Gate
`define BR_GATE_AND2(__iname__, __out__, __in0__, __in1__) \
br_gate_and2 br_gate_and2_``__iname__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .out(__out__) \
)

// 2-Input OR Gate
`define BR_GATE_OR2(__iname__, __out__, __in0__, __in1__) \
br_gate_or2 br_gate_or2_``__iname__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .out(__out__) \
)

// 2-Input XOR Gate
`define BR_GATE_XOR2(__iname__, __out__, __in0__, __in1__) \
br_gate_xor2 br_gate_xor2_``__iname__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .out(__out__) \
)

// 2-Input Mux Gate
`define BR_GATE_MUX2(__iname__, __out__, __in0__, __in1__, __sel__) \
br_gate_mux2 br_gate_mux2_``__iname__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .sel(__sel__), \
    .out(__out__) \
)

// 2-Input Clock Mux Gate
`define BR_GATE_CLK_MUX2(__iname__, __out__, __in0__, __in1__, __sel__) \
br_gate_or2 br_gate_or2_``__iname__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .sel(__sel__), \
    .out(__out__) \
)

// Integrated Clock Gate
`define BR_GATE_ICG(__iname__, __clk_out__, __clk_in__, __en__, __test_en__) \
br_gate_icg br_gate_icg_``__iname__`` ( \
    .clk_in(__clk_in__), \
    .en(__en__), \
    .test_en(__test_en__), \
    .clk_out(__clk_out__) \
)

// verilog_format: on

`endif  // BR_GATES_SVH
