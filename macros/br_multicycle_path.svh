// SPDX-License-Identifier: Apache-2.0


`ifndef BR_MULTICYCLE_PATH_SVH
`define BR_MULTICYCLE_PATH_SVH

// We implement the multicycle path macros using a module that encapsulates
// the path marker and optional assertions.

// Use this macro when a custom instance name suffix is required or desired.
// For example, use when __out__ is a complex expression.
`define BR_MCP_NAMED(__name__, __cycles__, __in__, __out__) \
br_cdc_multicycle_path #( \
    .Cycles(__cycles__), \
    .Width($bits(__out__)) \
) br_cdc_multicycle_path_``__name__ ( \
    .clk(clk), \
    .rst(rst), \
    .in(__in__), \
    .out(__out__) \
);

`define BR_RESET_ONLY_MCP_NAMED(__name__, __cycles__, __in__, __out__) \
br_cdc_multicycle_path #( \
    .Cycles(__cycles__), \
    .Width($bits(__out__)), \
    .AllowChangesOnlyInReset(1) \
) br_cdc_multicycle_path_``__name__ ( \
    .clk(clk), \
    .rst(rst), \
    .in(__in__), \
    .out(__out__) \
);

// Use these macros when __out__ is just a plain signal name.
`define BR_MCP(__cycles__, __in__, __out__) `BR_MCP_NAMED(__out__, __cycles__, __in__, __out__)
`define BR_RESET_ONLY_MCP(__cycles__, __in__, __out__) \
`BR_RESET_ONLY_MCP_NAMED(__out__, __cycles__, __in__, __out__)

`endif  // BR_MULTICYCLE_PATH_SVH
