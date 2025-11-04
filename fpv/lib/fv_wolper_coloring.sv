// SPDX-License-Identifier: Apache-2.0

// Reference: https://semiwiki.com/x-subscriber/oski-technology/7537-the-wolper-method/
// FV wolper coloring module
// This module checks/assumes (decided by parameter CheckMode) that in the input data stream,
// a specific bit (indicated by magic_bit_index) follows the pattern of 0000...11...0000.
// That is, two consecutive 1s will be injected at any random time in the data stream,
// Besides these two 1s, all other bits at magic_bit_index position should be 0.
// The module also includes coverage to count the number of valid data inputs.
`include "br_asserts.svh"
`include "br_registers.svh"

module fv_wolper_coloring #(
    // If CheckMode is 1, the module checks the property using assertions.
    // If CheckMode is 0, the module assumes the property using assumptions.
    parameter bit CheckMode = 1,
    parameter int DataWidth = 4,
    // Number of coverage points to be generated for valid data inputs
    parameter int NumCover  = 2
) (
    input logic clk,
    input logic rst,
    input logic [$clog2(DataWidth)-1:0] magic_bit_index,
    input logic valid,
    input logic [DataWidth-1:0] data
);

  // Integration Check
  `BR_ASSERT(magic_bit_index_range_a, $stable(magic_bit_index) && (magic_bit_index < DataWidth))

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
          state_n = data[magic_bit_index] ? S1 : S0;
        end
      end
      S1: begin
        if (valid) begin
          state_n = data[magic_bit_index] ? S2 : S_ERROR;
        end
      end
      S2: begin
        if (valid) begin
          state_n = data[magic_bit_index] ? S_ERROR : S2;
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
