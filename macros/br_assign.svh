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
`define BR_TO_LSB(__lhs__, __rhs__) \
  __lhs__[$bits(__rhs__) - 1:0] = __rhs__;

// Assign the most significant bits of a larger signal to a smaller signal.
`define BR_TRUNCATE_FROM_MSB(__lhs__, __rhs__) \
  __lhs__ = __rhs__[$bits(__rhs__) - 1 -: $bits(__lhs__)];

// Assign a smaller signal to the most significant bits of a larger signal.
`define BR_TO_MSB(__lhs__, __rhs__) \
  __lhs__[$bits(__lhs__) - 1 -: $bits(__rhs__)] = __rhs__;

`endif  // BR_ASSIGN_SVH
