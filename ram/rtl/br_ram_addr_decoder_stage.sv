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

// Bedrock-RTL Address Decoder Stage

`include "br_asserts_internal.svh"

module br_ram_addr_decoder_stage #(
    parameter int InputAddressWidth = 2,  // Width of the address. Must be at least 2.
    parameter int NumForks = 1,  // Number of output forks. Must be a positive power-of-2.
    localparam int ForkSelectWidth = $clog2(NumForks),  // Must be less than InputAddressWidth.
    localparam int OutputAddressWidth = InputAddressWidth - ForkSelectWidth
) (
    // Posedge-triggered clock.
    input  logic                                                 clk,
    // Synchronous active-high reset.
    input  logic                                                 rst,
    input  logic                                                 in_addr_valid,
    input  logic [InputAddressWidth-1:0]                         in_addr,
    output logic [         NumForks-1:0]                         out_addr_valid,
    output logic [         NumForks-1:0][OutputAddressWidth-1:0] out_addr
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(input_address_width_gte2_a, InputAddressWidth >= 2)
  `BR_ASSERT_STATIC(forks_gte1_a, NumForks >= 1)
  `BR_ASSERT_STATIC(forks_power_of_2_a, br_math::is_power_of_2(NumForks))
  `BR_ASSERT_STATIC(fork_select_width_correct_a, ForkSelectWidth < InputAddressWidth)

  // TODO(mgottscho): write more

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Base case: single fork, i.e., just a simple delay register
  if (NumForks == 1) begin : gen_fork_eq_1
    `BR_ASSERT_STATIC(output_address_width_correct_a, OutputAddressWidth == InputAddressWidth)

    br_delay_valid #(
        .BitWidth (OutputAddressWidth),
        .NumStages(1)
    ) br_delay_valid (
        .clk,
        .rst,
        .in_valid(in_addr_valid),
        .in(in_addr),
        .out_valid(out_addr_valid),
        .out(out_addr),
        .out_valid_stages(),  // unused
        .out_stages()  // unused
    );

    // Common case: multiple forks, i.e., requires decoding to one of the forks (replicated delay registers)
  end else begin : gen_fork_gt_1
    `BR_ASSERT_STATIC(output_address_width_correct_a, OutputAddressWidth < InputAddressWidth)

    localparam int SelectMsb = InputAddressWidth - 1;
    localparam int SelectLsb = (SelectMsb - ForkSelectWidth) + 1;

    `BR_ASSERT_STATIC(select_check_a, SelectMsb >= SelectLsb)

    logic [NumForks-1:0] fork_valid;

    // Replicate output registers to reduce fanout on each register
    for (genvar i = 0; i < NumForks; i++) begin : gen_fork
      assign fork_valid[i] = in_addr_valid && (in_addr[SelectMsb:SelectLsb] == i);

      br_delay_valid #(
          .BitWidth (OutputAddressWidth),
          .NumStages(1)
      ) br_delay_valid (
          .clk,
          .rst,
          .in_valid(fork_valid[i]),
          .in(in_addr[OutputAddressWidth-1:0]),
          .out_valid(out_addr_valid[i]),
          .out(out_addr[i]),
          .out_valid_stages(),  // unused
          .out_stages()  // unused
      );
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(valid_propagation_a, in_addr_valid |=> $onehot(out_addr_valid))
  `BR_ASSERT_IMPL(out_addr_valid_onehot0_a, $onehot0(out_addr_valid))
  for (genvar i = 0; i < NumForks; i++) begin : gen_fork_check
    `BR_ASSERT_IMPL(out_addr_correct_a,
                    out_addr_valid[i] |-> $past(
                        in_addr_valid
                    ) && (out_addr[i] == $past(
                        in_addr[OutputAddressWidth-1:0]
                    )))
  end

endmodule : br_ram_addr_decoder_stage
