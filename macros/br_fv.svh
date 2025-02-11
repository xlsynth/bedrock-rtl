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

`include "br_asserts.svh"
`ifndef BR_FV_SVH
`define BR_FV_SVH

////////////////////////////////////////////////////////////////////////////////
// Common macros for Formal Property Verification
////////////////////////////////////////////////////////////////////////////////

// pick two random and unique indices
`define BR_FV_2RAND_IDX(__i__, __j__, __n__) \
`BR_ASSUME(asm_index_i, $stable(__i__) && (__i__ < __n__)) \
`BR_ASSUME(asm_index_j, $stable(__j__) && (__j__ < __n__)) \
`BR_ASSUME(asm_unique_index, __i__ != __j__)

// find which index is 1 for onehot vector
`define BR_FV_IDX(__index__, __vec__, __n__) \
always_comb begin \
  __index__ = 0; \
  for (int i = 0; i < __n__; i++) begin \
    if (__vec__[i]) begin \
      __index__ = i; \
    end \
  end \
end

`endif  // BR_FV_SVH
