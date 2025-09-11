// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_enc_bin2gray #(
    parameter int Width = 2  // Must be at least 2
) (
    input  logic [Width-1:0] bin,
    output logic [Width-1:0] gray
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_gte_2_a, Width >= 2)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [Width-1:0] bin_offset;

  assign bin_offset = {1'b0, bin[Width-1:1]};
  assign gray = bin_offset ^ bin;

endmodule : br_enc_bin2gray
