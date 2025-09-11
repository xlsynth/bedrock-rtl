// SPDX-License-Identifier: Apache-2.0

`ifndef BR_ASSIGN_SVH
`define BR_ASSIGN_SVH

// Zero-extend a smaller signal to a larger signal.
`define BR_ZERO_EXT(__lhs__, __rhs__) \
  __lhs__ = {{($bits(__lhs__) - $bits(__rhs__)){1'b0}}, __rhs__};

// Zero-extend a signal if it's smaller than the target signal.
`define BR_ASSIGN_MAYBE_ZERO_EXT(__name__, __lhs__, __rhs__) \
  if ($bits(__lhs__) > $bits(__rhs__)) begin : gen_zero_ext_``__name__ \
    assign `BR_ZERO_EXT(__lhs__, __rhs__) \
  end else begin : gen_zero_ext_same_width``__name__ \
    assign __lhs__ = __rhs__; \
  end

// Assign the least significant bits of a larger signal to a smaller signal.
`define BR_TRUNCATE_FROM_LSB(__lhs__, __rhs__) \
  __lhs__ = __rhs__[$bits(__lhs__) - 1:0];

// Assign a smaller signal to the least significant bits of a larger signal.
`define BR_INSERT_TO_LSB(__lhs__, __rhs__) \
  __lhs__[$bits(__rhs__) - 1:0] = __rhs__;

// Assign the most significant bits of a larger signal to a smaller signal.
`define BR_TRUNCATE_FROM_MSB(__lhs__, __rhs__) \
  __lhs__ = __rhs__[$bits(__rhs__) - 1 -: $bits(__lhs__)];

// Assign a smaller signal to the most significant bits of a larger signal.
`define BR_INSERT_TO_MSB(__lhs__, __rhs__) \
  __lhs__[$bits(__lhs__) - 1 -: $bits(__rhs__)] = __rhs__;

`endif  // BR_ASSIGN_SVH
