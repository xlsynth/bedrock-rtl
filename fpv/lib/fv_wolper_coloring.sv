// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module fv_wolper_coloring #(
    parameter bit CheckMode = 1,
    parameter int DataWidth = 4,
    parameter int NumCover  = 2
) (
    input logic clk,
    input logic rst,
    input logic [$clog2(DataWidth)-1:0] magic_bit,
    input logic valid,
    input logic [DataWidth-1:0] data
);

  // Integration Check
  `BR_ASSERT(magic_bit_range_a, $stable(magic_bit) && (magic_bit < DataWidth))

  typedef enum logic [1:0] {
    S0,      // start state: only 0 has been received
    S1,      // One 1 is received
    S2,      // Two 1s are received
    S_ERROR  // error state
  } state_t;

  state_t state, state_n;
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
    end else begin
      state <= state_n;
    end
  end

  always_comb begin
    state_n = state;
    unique case (state)
      S0: begin
        if (valid) begin
          state_n = data[magic_bit] ? S1 : S0;
        end
      end
      S1: begin
        if (valid) begin
          state_n = data[magic_bit] ? S2 : S_ERROR;
        end
      end
      S2: begin
        if (valid) begin
          state_n = data[magic_bit] ? S_ERROR : S2;
        end
      end
      S_ERROR: begin
        // stay in error state
      end
    endcase
  end

  if (CheckMode) begin : gen_ast
    `BR_ASSERT(no_error_state_a, state != S_ERROR)
  end else begin : gen_asm
    `BR_ASSUME(no_error_state_a, state != S_ERROR)
  end

  logic [$clog2(NumCover):0] cover_count;
  `BR_REGL(cover_count, cover_count + 'd1, valid)
  for (genvar i = 1; i <= NumCover; i++) begin : gen_cover
    `BR_COVER(num_of_valid_data_c, cover_count == i)
  end

endmodule
