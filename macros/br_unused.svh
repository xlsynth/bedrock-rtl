// SPDX-License-Identifier: Apache-2.0


`ifndef BR_UNUSED_SVH
`define BR_UNUSED_SVH

// Use this macro when a custom instance name suffix is required or desired.
// For example, use when __x__ is a complex expression (e.g., concatenation like {foo, bar}).
`define BR_UNUSED_NAMED(__name__, __x__) \
br_misc_unused #( \
    .Width($bits(__x__))) \
br_misc_unused_``__name__ ( \
    .in(__x__) \
);

// Use this macro when __x__ is just a plain signal name.
`define BR_UNUSED(__x__) `BR_UNUSED_NAMED(__x__, __x__)

// Use for temporary unused signals.
// Intended to make temporary unused easier to find and resolve.
`define BR_UNUSED_TODO(__name__, __x__) `BR_UNUSED_NAMED(__name__, __x__)

`endif  // BR_UNUSED_SVH
