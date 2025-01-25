`include "br_assign.svh"

module br_assign_test #(
    parameter int L = 15,
    parameter int S = 7,
    localparam type large_t = logic [L-1:0],
    localparam type small_t = logic [S-1:0]
) (
    input large_t large_in,
    input small_t small_in,
    output small_t [1:0] small_out,
    output large_t [4:0] large_out
);
  assign `BR_ZERO_EXT(large_out[0], small_in)
  assign `BR_TRUNCATE_FROM_LSB(small_out[0], large_in)
  assign `BR_TRUNCATE_FROM_MSB(small_out[1], large_in)

  assign `BR_TO_LSB(large_out[1], small_in)
  assign large_out[1][L-1:S] = '0;

  assign `BR_TO_MSB(large_out[2], small_in)
  assign large_out[2][L-S-1:0] = '0;

  `BR_ASSIGN_MAYBE_ZERO_EXT(extend, large_out[3], small_in)
  `BR_ASSIGN_MAYBE_ZERO_EXT(no_extend, large_out[4], large_in)

endmodule : br_assign_test
