// SPDX-License-Identifier: Apache-2.0

`ifndef BR_TIEOFF_SVH
`define BR_TIEOFF_SVH

// We implement the tie-off macros using modules that encapsulate the
// actual signal assignment. It's super gross but this way we can
// leverage inline lint waivers (inside the br_misc_tieoff_* module bodies).

// Use for permanent '0 tie-off where __x__ is an expression.
`define BR_TIEOFF_ZERO_NAMED(__name__, __x__) \
br_misc_tieoff_zero #( \
    .Width($bits(__x__)) \
) br_misc_tieoff_zero_``__name__ ( \
    .out(__x__) \
);

// Use for permanent '1 tie-off where __x__ is an expression.
`define BR_TIEOFF_ONE_NAMED(__name__, __x__) \
br_misc_tieoff_one #( \
    .Width($bits(__x__)) \
) br_misc_tieoff_one_``__name__ ( \
    .out(__x__) \
);

// Use for permanent '0 tie-off where __x__ is a signal name.
`define BR_TIEOFF_ZERO(__x__) `BR_TIEOFF_ZERO_NAMED(__x__, __x__)

// Use for permanent '1 tie-off where __x__ is a signal name.
`define BR_TIEOFF_ONE(__x__) `BR_TIEOFF_ONE_NAMED(__x__, __x__)

// Use for temporary '0 tie-off.
// Intended to make temporary tieoffs easier to find and resolve.
`define BR_TIEOFF_ZERO_TODO(__name__, __x__) `BR_TIEOFF_ZERO_NAMED(__name__, __x__)

// Use for temporary '1 tie-off.
// Intended to make temporary tieoffs easier to find and resolve.
`define BR_TIEOFF_ONE_TODO(__name__, __x__) `BR_TIEOFF_ONE_NAMED(__name__, __x__)

`endif  // BR_TIEOFF_SVH
