// SPDX-License-Identifier: Apache-2.0


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

// verilog_lint: waive-start line-length
// verilog_format: off

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
`define BR_REGLI(__q__, __d__, __en__, __init__) \
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
`define BR_REGALI(__q__, __d__, __en__, __init__) \
always_ff @(posedge clk or posedge arst) begin \
    if (arst) __q__ <= __init__; \
    else if (__en__) __q__ <= __d__; \
end

////////////////////////////////////////////////////////////////////////////////
// Asynchronous active-high reset registers -- custom clock, reset
////////////////////////////////////////////////////////////////////////////////

// Flip-flop register
// * unconditional load
// * initial value is 0
// * asynchronous active-high reset
// * positive-edge triggered clock
`define BR_REGAX(__q__, __d__, __clk__, __arst__) \
always_ff @(posedge __clk__ or posedge __arst__) begin \
    if (__arst__) __q__ <= '0; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value is 0
// * asynchronous active-high reset
// * positive-edge triggered clock
`define BR_REGALX(__q__, __d__, __en__, __clk__, __arst__) \
always_ff @(posedge __clk__ or posedge __arst__) begin \
    if (__arst__) __q__ <= '0; \
    else if (__en__) __q__ <= __d__; \
end

// Flip-flop register
// * unconditional load
// * initial value given
// * asynchronous active-high reset
// * positive-edge triggered clock
`define BR_REGAIX(__q__, __d__, __init__, __clk__, __arst__) \
always_ff @(posedge __clk__ or posedge __arst__) begin \
    if (__arst__) __q__ <= __init__; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value given
// * asynchronous active-high reset
// * positive-edge triggered clock
`define BR_REGALIX(__q__, __d__, __en__, __init__, __clk__, __arst__) \
always_ff @(posedge __clk__ or posedge __arst__) begin \
    if (__arst__) __q__ <= __init__; \
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
`define BR_REGX(__q__, __d__, __clk__, __rst__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= '0; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value is 0
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGLX(__q__, __d__, __en__, __clk__, __rst__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= '0; \
    else if (__en__) __q__ <= __d__; \
end

// Flip-flop register
// * unconditional load
// * initial value given
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGIX(__q__, __d__, __init__, __clk__, __rst__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= __init__; \
    else __q__ <= __d__; \
end

// Flip-flop register
// * conditional load enable
// * initial value given
// * synchronous active-high reset
// * positive-edge triggered clock
`define BR_REGLIX(__q__, __d__, __en__, __init__, __clk__, __rst__) \
always_ff @(posedge __clk__) begin \
    if (__rst__) __q__ <= __init__; \
    else if (__en__) __q__ <= __d__; \
end

// Flip-flop register
// * unconditional load
// * no reset
// * positive-edge triggered clock
`define BR_REGNX(__q__, __d__, __clk__) \
always_ff @(posedge __clk__) begin \
    __q__ <= __d__; \
end

// Flip-flop register
// * conditional load
// * no reset
// * positive-edge triggered clock
`define BR_REGLNX(__q__, __d__, __en__, __clk__) \
always_ff @(posedge __clk__) begin \
    if (__en__) __q__ <= __d__; \
end

////////////////////////////////////////////////////////////////////////////////
// NOSCAN registers -- custom clock, reset
////////////////////////////////////////////////////////////////////////////////

// These macros instantiate one br_gate flip-flop per bit. Include the target
// technology's gate library (or br_gate_mock for behavioral simulation).
// __q__ must be a scalar or packed signal identifier; it names the instance array.
// Both the instances and the mock's storage carry the _NOSCAN suffix.
// Resets at the macro interface remain active-high; the asynchronous variants
// invert reset for the gate primitive's active-low arst_n port.

// Flip-flop register without scan
// * unconditional load, no reset
// * explicit positive-edge triggered clock
`define BR_REGNX_NOSCAN(__q__, __d__, __clk__) \
br_gate_dff_noscan __q__``_reg_NOSCAN [$bits(__q__)-1:0] ( \
    .clk(__clk__), \
    .in($bits(__q__)'(__d__)), \
    .out(__q__) \
);

// Flip-flop register without scan
// * unconditional load, reset value 0
// * explicit synchronous active-high reset and positive-edge triggered clock
`define BR_REGX_NOSCAN(__q__, __d__, __clk__, __rst__) \
br_gate_dff_noscan __q__``_reg_NOSCAN [$bits(__q__)-1:0] ( \
    .clk(__clk__), \
    .in((__rst__) ? '0 : $bits(__q__)'(__d__)), \
    .out(__q__) \
);

// Flip-flop register without scan
// * conditional load enable, reset value 0 (reset takes priority over enable)
// * explicit synchronous active-high reset and positive-edge triggered clock
`define BR_REGLX_NOSCAN(__q__, __d__, __en__, __clk__, __rst__) \
br_gate_dff_noscan __q__``_reg_NOSCAN [$bits(__q__)-1:0] ( \
    .clk(__clk__), \
    .in((__rst__) ? '0 : ((__en__) ? $bits(__q__)'(__d__) : (__q__))), \
    .out(__q__) \
);

// Flip-flop register without scan
// * unconditional load, reset value 0
// * explicit asynchronous active-high reset and positive-edge triggered clock
`define BR_REGAX_NOSCAN(__q__, __d__, __clk__, __arst__) \
br_gate_dff_arst_noscan __q__``_reg_NOSCAN [$bits(__q__)-1:0] ( \
    .clk(__clk__), \
    .arst_n(!(__arst__)), \
    .in($bits(__q__)'(__d__)), \
    .out(__q__) \
);

// Flip-flop register without scan
// * conditional load enable, reset value 0 (reset takes priority over enable)
// * explicit asynchronous active-high reset and positive-edge triggered clock
`define BR_REGALX_NOSCAN(__q__, __d__, __en__, __clk__, __arst__) \
br_gate_dff_arst_noscan __q__``_reg_NOSCAN [$bits(__q__)-1:0] ( \
    .clk(__clk__), \
    .arst_n(!(__arst__)), \
    .in((__en__) ? $bits(__q__)'(__d__) : (__q__)), \
    .out(__q__) \
);

// verilog_lint: waive-stop line-length
// verilog_format: on

`endif  // BR_REGISTERS_SVH
