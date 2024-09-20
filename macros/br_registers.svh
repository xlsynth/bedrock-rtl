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

`ifndef BR_REGISTERS_SVH
`define BR_REGISTERS_SVH

// Common macros for instantiating registers in a design.
// They help make RTL code easier to write, read, and maintain by hiding
// the implementation boilerplate for clocking, reset, and load enables.
//
// The SystemVerilog language lacks native support for namespacing.
// Therefore we namespace all macros with the BR_ prefix (stands for Bedrock).

////////////////////////////////////////////////////////////////////////////////
// Non-resettable registers -- clk
////////////////////////////////////////////////////////////////////////////////

// Flip-flop register
// * unconditional load
// * no reset
// * positive-edge triggered clock named 'clk'
`define BR_REGN(__q__, __d__) \
always_ff @(posedge clk) begin \
    __q__ <= __d__; \
end

// Flip-flop register
// * load enable
// * no reset
// * positive-edge triggered clock named 'clk'
`define BR_REGLN(__q__, __d__, __en__) \
always_ff @(posedge clk) begin \
    if (__en__) __q__ <= __d__; \
end

////////////////////////////////////////////////////////////////////////////////
// Synchronous active-high reset registers -- clk, rst
////////////////////////////////////////////////////////////////////////////////

// Flip-flop register
// * unconditional load
// * initial value is 0
// * synchronous active-high reset named 'rst'
// * positive-edge triggered clock named 'clk'
`define BR_REG(__q__, __d__) \
always_ff @(posedge clk) begin \
    if (rst) __q__ <= '0; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value is 0
// * synchronous active-high reset named 'rst'
// * positive-edge triggered clock named 'clk'
`define BR_REGL(__q__, __d__, __en__) \
always_ff @(posedge clk) begin \
    if (rst) __q__ <= '0; \
    else if (__en__) __q__ <= __d__; \
end

// Flip-flop register
// * unconditional load
// * initial value given
// * synchronous active-high reset named 'rst'
// * positive-edge triggered clock named 'clk'
`define BR_REGI(__q__, __d__, __init__) \
always_ff @(posedge clk) begin \
    if (rst) __q__ <= __init__; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value given
// * synchronous active-high reset named 'rst'
// * positive-edge triggered clock named 'clk'
`define BR_REGIL(__q__, __d__, __en__, __init__) \
always_ff @(posedge clk) begin \
    if (rst) __q__ <= __init__; \
    else if (__en__) __q__ <= __d__; \
end

////////////////////////////////////////////////////////////////////////////////
// Asynchronous active-high reset registers -- clk, arst
////////////////////////////////////////////////////////////////////////////////

// Flip-flop register
// * unconditional load
// * initial value is 0
// * asynchronous active-high reset named 'arst'
// * positive-edge triggered clock named 'clk'
`define BR_REGA(__q__, __d__) \
always_ff @(posedge clk or posedge arst) begin \
    if (arst) __q__ <= '0; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value is 0
// * asynchronous active-high reset named 'arst'
// * positive-edge triggered clock named 'clk'
`define BR_REGAL(__q__, __d__, __en__) \
always_ff @(posedge clk or posedge arst) begin \
    if (arst) __q__ <= '0; \
    else if (__en__) __q__ <= __d__; \
end

// Flip-flop register
// * unconditional load
// * initial value given
// * asynchronous active-high reset named 'arst'
// * positive-edge triggered clock named 'clk'
`define BR_REGAI(__q__, __d__, __init__) \
always_ff @(posedge clk or posedge arst) begin \
    if (arst) __q__ <= __init__; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value given
// * asynchronous active-high reset named 'arst'
// * positive-edge triggered clock named 'clk'
`define BR_REGAIL(__q__, __d__, __en__, __init__) \
always_ff @(posedge clk or posedge arst) begin \
    if (arst) __q__ <= __init__; \
    else if (__en__) __q__ <= __d__; \
end

////////////////////////////////////////////////////////////////////////////////
// Synchronous active-high reset registers -- custom clock, reset
////////////////////////////////////////////////////////////////////////////////

// Flip-flop register
// * unconditional load
// * initial value is 0
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGX(__q__, __d__, __rst__, __clk__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= '0; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value is 0
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGLX(__q__, __d__, __en__, __rst__, __clk__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= '0; \
    else if (__en__) __q__ <= __d__; \
end

// Flip-flop register
// * unconditional load
// * initial value given
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGIX(__q__, __d__, __init__, __rst__, __clk__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= __init__; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value given
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGILX(__q__, __d__, __en__, __init__, __rst__, __clk__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= __init__; \
    else if (__en__) __q__ <= __d__; \
end


`endif // BR_REGISTERS_SVH
