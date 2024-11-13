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
//
// TODO(mgottscho): description

`include "br_asserts_internal.svh"

module br_ram_addr_decoder_stage #(
    // Width of the address. Must be at least 1.
    parameter int InputAddressWidth = 1,
    // Sideband signals to pipeline in lockstep with the address decoding.
    // Safe to tie-off if not used. Must be at least 1.
    parameter int DataWidth = 1,
    parameter int Fanout = 1,  // Number of output fanout. Must be a positive power-of-2.
    parameter bit RegisterOutputs = 0,  // If 1, then pipeline latency is 1 cycle; else, 0 cycles.
    localparam int FanoutSelectWidth = $clog2(Fanout),  // Must be less than InputAddressWidth.
    localparam int OutputAddressWidth = InputAddressWidth - FanoutSelectWidth
) (
    // Posedge-triggered clock.
    // Can be unused if RegisterOutputs == 0.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 clk,
    // Synchronous active-high reset.
    // Can be unused if RegisterOutputs == 0.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 rst,
    input  logic                                                 in_valid,
    input  logic [InputAddressWidth-1:0]                         in_addr,
    input  logic [        DataWidth-1:0]                         in_data,
    output logic [           Fanout-1:0]                         out_valid,
    output logic [           Fanout-1:0][OutputAddressWidth-1:0] out_addr,
    output logic [           Fanout-1:0][         DataWidth-1:0] out_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(input_address_width_gte1_a, InputAddressWidth >= 1)
  `BR_ASSERT_STATIC(fanout_gte1_a, Fanout >= 1)
  `BR_ASSERT_STATIC(fanout_power_of_2_a, br_math::is_power_of_2(Fanout))
  `BR_ASSERT_STATIC(fanout_select_width_correct_a, FanoutSelectWidth < InputAddressWidth)
  `BR_ASSERT_STATIC(output_address_gt0_a, OutputAddressWidth > 0)

  // TODO(mgottscho): write more

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Base case: single fanout, i.e., just a simple delay register
  if (Fanout == 1) begin : gen_fanout_eq_1
    `BR_ASSERT_STATIC(output_address_width_ok_a, OutputAddressWidth == InputAddressWidth)

    br_delay_valid #(
        .BitWidth (OutputAddressWidth + DataWidth),
        .NumStages(RegisterOutputs ? 1 : 0)
    ) br_delay_valid (
        .clk,
        .rst,
        .in_valid(in_valid),
        .in({in_addr, in_data}),
        .out_valid(out_valid),
        .out({out_addr, out_data}),
        .out_valid_stages(),  // unused
        .out_stages()  // unused
    );

    // Common case: multiple fanout, i.e., requires decoding to one of them (replicated delay registers)
  end else begin : gen_fanout_gt_1
    `BR_ASSERT_STATIC(output_address_width_ok_a, OutputAddressWidth < InputAddressWidth)

    localparam int SelectMsb = InputAddressWidth - 1;
    localparam int SelectLsb = (SelectMsb - FanoutSelectWidth) + 1;

    `BR_ASSERT_STATIC(select_check_a, SelectMsb >= SelectLsb)

    logic [Fanout-1:0] fanout_valid;

    // Replicate output registers to reduce fanout on each register
    for (genvar i = 0; i < Fanout; i++) begin : gen_fanout
      assign fanout_valid[i] = in_valid && (in_addr[SelectMsb:SelectLsb] == i);

      br_delay_valid #(
          .BitWidth (OutputAddressWidth + DataWidth),
          .NumStages(RegisterOutputs ? 1 : 0)
      ) br_delay_valid (
          .clk,
          .rst,
          .in_valid(fanout_valid[i]),
          .in({in_addr[OutputAddressWidth-1:0], in_data}),
          .out_valid(out_valid[i]),
          .out({out_addr[i], out_data[i]}),
          .out_valid_stages(),  // unused
          .out_stages()  // unused
      );
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(out_valid_onehot0_a, $onehot0(out_valid))

  if (RegisterOutputs) begin : gen_impl_checks_registered
    `BR_ASSERT_IMPL(valid_propagation_a, in_valid |=> $onehot(out_valid))
    for (genvar i = 0; i < Fanout; i++) begin : gen_fanout_check
      `BR_ASSERT_IMPL(out_addr_correct_a,
                      out_valid[i] |-> $past(
                          in_valid
                      ) && (out_addr[i] == $past(
                          in_addr[OutputAddressWidth-1:0]
                      )))
    end
  end else begin : gen_impl_checks_not_registered
    `BR_ASSERT_IMPL(valid_propagation_a, in_valid |-> $onehot(out_valid))
    for (genvar i = 0; i < Fanout; i++) begin : gen_fanout_check
      `BR_ASSERT_IMPL(out_addr_correct_a,
                      out_valid[i] |-> in_valid && (out_addr[i] == in_addr[OutputAddressWidth-1:0]))
    end
  end

endmodule : br_ram_addr_decoder_stage
