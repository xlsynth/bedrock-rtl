// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Delay Shift Register
//
// Implements a loadable shift register with a shift enable input.
// The contents of the shift register are initialized to the 'initial_value'
// at reset or upon assertion of the 'reinit' input. Asserting both 'reinit'
// and 'shift_en' concurrently will load in a shifted version of 'initial_value'
// along with 'shift_in' data.
//

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_shift_reg #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 1,  // Must be at least 1
    // If 1, cover the cases where reinit is asserted.
    // If 0, assert that reinit is never asserted.
    parameter bit EnableCoverReinit = 1
) (
    input  logic                            clk,
    input  logic                            rst,
    // value gets set to initial_value on reset or when reinit is asserted
    input  logic                            reinit,
    input  logic [NumStages-1:0][Width-1:0] initial_value,
    output logic [NumStages-1:0][Width-1:0] value,
    // when shift_en is 1 and reinit is 0, value becomes {value[NumStages-2:0], shift_in}
    // when shift_en is 1 and reinit is 1, value becomes {initial_value[NumStages-2:0], shift_in}
    input  logic                            shift_en,
    input  logic [    Width-1:0]            shift_in,
    // shift_out is the same as value[NumStages-1]
    output logic [    Width-1:0]            shift_out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_one_a, NumStages >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages-1:0][Width-1:0] stages, stages_next, stages_temp;

  assign stages_temp = (reinit) ? initial_value : stages;

  if (NumStages == 1) begin : gen_one_stage
    assign stages_next = (shift_en) ? shift_in : stages_temp;
  end else begin : gen_multi_stage
    assign stages_next = (shift_en) ? {stages_temp[NumStages-2:0], shift_in} : stages_temp;
  end

  `BR_REGLI(stages, stages_next, shift_en || reinit, initial_value)

  assign shift_out = stages[NumStages-1];
  assign value = stages;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (EnableCoverReinit) begin : gen_cover_reinit
    `BR_ASSERT_IMPL(value_initialized_a, (!shift_en && reinit) |=> value == $past(initial_value))
  end else begin : gen_assert_no_reinit
    `BR_ASSERT_IMPL(no_reinit_a, !reinit)
  end
  `BR_ASSERT_IMPL(value_stable_a, (!shift_en && !reinit) |=> $stable(value))

  if (NumStages == 1) begin : gen_assert_one_stage
    `BR_ASSERT_IMPL(value_shifted_a, shift_en |=> value == $past(shift_in))
  end else begin : gen_assert_multi_stage
    if (EnableCoverReinit) begin : gen_cover_reinit_with_shift
      `BR_ASSERT_IMPL(
          value_shifted_with_reinit_a,
          (shift_en && reinit) |=> value == $past({initial_value[NumStages-2:0], shift_in}))
    end
    `BR_ASSERT_IMPL(value_shifted_without_reinit_a,
                    (shift_en && !reinit) |=> value == $past({stages[NumStages-2:0], shift_in}))
  end

endmodule : br_delay_shift_reg
