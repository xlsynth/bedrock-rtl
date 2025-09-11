// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_enc_countones #(
    parameter int Width = 1,  // Must be at least 1
    localparam int CountWidth = $clog2(Width + 1)
) (
    input logic [Width-1:0] in,
    output logic [CountWidth-1:0] count
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    count = 0;
    for (int i = 0; i < Width; i++) begin
      count += in[i];
    end
  end

endmodule : br_enc_countones
