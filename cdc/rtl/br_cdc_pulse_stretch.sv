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

// CDC synchronizer and pulse stretcher.
//
// This module synchronizes a pulse signal from a source clock domain to a
// destination clock domain and stretches the pulse to one cycle of the
// destination clock domain. The input pulse signal is used as the clock for
// a flop, so this circuit can only be used if the pulse width is at least as
// wide as the flop min pulse width. Also, if two pulses are close together,
// the destination domain may only see one pulse.

`include "br_asserts.svh"
`include "br_gates.svh"
`include "br_registers.svh"

module br_cdc_pulse_stretch #(
    // Number of synchronization stages. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumStages = 3
) (
    input logic src_pulse,  // ri lint_check_waive CLOCK_NAME

    input  logic dst_clk,   // ri lint_check_waive ONE_LOCAL_CLOCK
    input  logic dst_rst,
    output logic dst_pulse
);

  // Integration Assertions
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_one_a, NumStages >= 1)

  // Implementation

  logic src_pulse_capture;
  logic dst_bit;
  logic dst_bit_d;  // ri lint_check_waive RESET_NAME

  // Use the source pulse to capture a 1'b1. It will be cleared asynchronously when it is
  // synchronized to the destination clock domain.
  // ri lint_check_off RESET_LEVEL CONST_FF
  `BR_REGAX(src_pulse_capture, 1'b1, src_pulse, dst_bit_d)
  // ri lint_check_on RESET_LEVEL CONST_FF

  br_gate_cdc_sync #(
      .NumStages(NumStages)
  ) br_gate_cdc_sync (
      .clk(dst_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .in(src_pulse_capture),
      .out(dst_bit)
  );

  // ri lint_check_off RESET_USE RESET_DRIVER
  `BR_REGX(dst_bit_d, dst_bit, dst_clk, dst_rst)
  // ri lint_check_on RESET_USE RESET_DRIVER

  assign dst_pulse = dst_bit & ~dst_bit_d;  // ri lint_check_waive RESET_USE

endmodule
