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

// 2-Input AND Gate
`define BR_GATE_AND2(__iname__, __out__, __in1__, __in2__) \
br_gate_and2 br_gate_and2_``__iname__`` ( \
    .in1(__in1__), \
    .in2(__in2__), \
    .out(__out__) \
)

// 2-Input OR Gate
`define BR_GATE_OR2(__iname__, __out__, __in1__, __in2__) \
br_gate_or2 br_gate_or2_``__iname__`` ( \
    .in1(__in1__), \
    .in2(__in2__), \
    .out(__out__) \
)

// verilog_format: on

`endif  // BR_GATES_SVH
