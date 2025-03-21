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
`define BR_GATE_BUF(__out__, __in__) \
br_gate_buf br_gate_buf_``__out__`` ( \
    .in(__in__), \
    .out(__out__) \
);

// Clock Buffer
`define BR_GATE_CLK_BUF(__out__, __in__) \
br_gate_clk_buf br_gate_clk_buf_``__out__`` ( \
    .in(__in__), \
    .out(__out__) \
);

// Clock Inverter
`define BR_GATE_CLK_INV(__out__, __in__) \
br_gate_clk_inv br_gate_clk_inv_``__out__`` ( \
    .in(__in__), \
    .out(__out__) \
);

// Inverter
`define BR_GATE_INV(__out__, __in__) \
br_gate_inv br_gate_inv_``__out__`` ( \
    .in(__in__), \
    .out(__out__) \
);

// 2-Input AND Gate
`define BR_GATE_AND2(__out__, __in0__, __in1__) \
br_gate_and2 br_gate_and2_``__out__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .out(__out__) \
);

// 2-Input OR Gate
`define BR_GATE_OR2(__out__, __in0__, __in1__) \
br_gate_or2 br_gate_or2_``__out__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .out(__out__) \
);

// 2-Input XOR Gate
`define BR_GATE_XOR2(__out__, __in0__, __in1__) \
br_gate_xor2 br_gate_xor2_``__out__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .out(__out__) \
);

// 2-Input Mux Gate
`define BR_GATE_MUX2(__out__, __in0__, __in1__, __sel__) \
br_gate_mux2 br_gate_mux2_``__out__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .sel(__sel__), \
    .out(__out__) \
);

// 2-Input Clock Mux Gate
`define BR_GATE_CLK_MUX2(__out__, __in0__, __in1__, __sel__) \
br_gate_clk_mux2 br_gate_clk_mux2_``__out__`` ( \
    .in0(__in0__), \
    .in1(__in1__), \
    .sel(__sel__), \
    .out(__out__) \
);

// Integrated Clock Gate
`define BR_GATE_ICG(__clk_out__, __clk_in__, __en__) \
br_gate_icg br_gate_icg_``__clk_out__`` ( \
    .clk_in(__clk_in__), \
    .en(__en__), \
    .clk_out(__clk_out__) \
);

// Integrated Clock Gate with Synchronous Reset
`define BR_GATE_ICG_RST(__clk_out__, __clk_in__, __en__, __rst__) \
br_gate_icg_rst br_gate_icg_rst_``__clk_out__`` ( \
    .clk_in(__clk_in__), \
    .en(__en__), \
    .rst(__rst__), \
    .clk_out(__clk_out__) \
);

// Clock Domain Crossing Synchronizer with default number of stages
`define BR_GATE_CDC_SYNC(__out__, __in__, __clk__) \
br_gate_cdc_sync br_gate_cdc_sync_``__out__`` ( \
    .clk(__clk__), \
    .in(__in__), \
    .out(__out__) \
);

// Clock Domain Crossing Synchronizer with configurable number of stages
`define BR_GATE_CDC_SYNC_STAGES(__out__, __in__, __clk__, __stages__) \
br_gate_cdc_sync #(__stages__) br_gate_cdc_sync_``__out__`` ( \
    .clk(__clk__), \
    .in(__in__), \
    .out(__out__) \
);

// Clock Domain Crossing Synchronizer with Asynchronous Reset and default number of stages
`define BR_GATE_CDC_SYNC_ARST(__out__, __in__, __clk__, __arst__) \
br_gate_cdc_sync_arst br_gate_cdc_sync_arst_``__out__`` ( \
    .clk(__clk__), \
    .arst(__arst__), \
    .in(__in__), \
    .out(__out__) \
);

// Clock Domain Crossing Synchronizer with Asynchronous Reset and configurable number of stages
`define BR_GATE_CDC_SYNC_ARST_STAGES(__out__, __in__, __clk__, __arst__, __stages__) \
br_gate_cdc_sync_arst #(__stages__) br_gate_cdc_sync_arst_``__out__`` ( \
    .clk(__clk__), \
    .arst(__arst__), \
    .in(__in__), \
    .out(__out__) \
);

// Reset Synchronizer
`define BR_GATE_CDC_RST_SYNC(__srst__, __arst__, __clk__) \
br_cdc_rst_sync #(__stages__) br_cdc_rst_sync_``__srst__`` ( \
    .clk(__clk__), \
    .arst(__arst__), \
    .srst(__srst__) \
);

// Reset Synchronizer with configurable number of stages
`define BR_GATE_CDC_RST_SYNC_STAGES(__srst__, __arst__, __clk__, __stages__) \
br_cdc_rst_sync #(__stages__) br_cdc_rst_sync_``__srst__`` ( \
    .clk(__clk__), \
    .arst(__arst__), \
    .srst(__srst__) \
);

// Buffer used at CDC crossings but when the signal is considered pseudo-static. In other words,
// this signal will be stable before the destination domain is out of reset and the clock is
// running.
`define BR_GATE_CDC_PSEUDOSTATIC(__out__, __in__) \
br_gate_cdc_pseudostatic br_gate_cdc_pseudostatic_``__out__`` ( \
    .in(__in__), \
    .out(__out__) \
);

`define BR_GATE_CDC_PSEUDOSTATIC_BUS(__out__, __in__, __width__) \
br_gate_cdc_pseudostatic br_gate_cdc_pseudostatic_``__out__`` [``__width__``-1:0] ( \
    .in(__in__), \
    .out(__out__) \
);

// Buffer used at CDC crossings that indicate that this crossing would need to be checked for
// max delay (skew checks).
`define BR_GATE_CDC_MAXDEL(__out__, __in__) \
br_gate_cdc_maxdel br_gate_cdc_maxdel_``__out__`` ( \
    .in(__in__), \
    .out(__out__) \
);

`define BR_GATE_CDC_MAXDEL_BUS(__out__, __in__, __width__) \
br_gate_cdc_maxdel br_gate_cdc_maxdel_``__out__`` [``__width__``-1:0] ( \
    .in(__in__), \
    .out(__out__) \
);

// verilog_format: on

`endif  // BR_GATES_SVH
