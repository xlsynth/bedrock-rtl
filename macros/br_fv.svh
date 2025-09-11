// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`ifndef BR_FV_SVH
`define BR_FV_SVH

////////////////////////////////////////////////////////////////////////////////
// Common macros for Formal Property Verification
////////////////////////////////////////////////////////////////////////////////

// pick two random and unique indices
`define BR_FV_2RAND_IDX(__i__, __j__, __n__) \
`BR_ASSUME(asm_index_``__i__``, $stable(__i__) && (__i__ < __n__)) \
`BR_ASSUME(asm_index_``__j__``, $stable(__j__) && (__j__ < __n__)) \
`BR_ASSUME(asm_unique_``__i__``_``__j__``, __i__ != __j__)

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
