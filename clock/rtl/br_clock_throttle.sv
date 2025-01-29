// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Clock Throttle
//
// Throttles a clock signal by swallowing pulses. An external trigger is used to
// control the throttling, and can be either synchronous or asynchronous to the
// input clock. The skip_value is used to control the number of clock cycles to
// skip with a trigger event occurs.

`include "br_asserts_internal.svh"

module br_clock_throttle #(
    parameter int CntrWidth   = 1,  // must be at least 1
    parameter bit SyncTrigger = 1   // 0 for async trigger, 1 for sync trigger
) (
    // Input clock
    input logic clk_in,
    // Synchronous active-high reset
    input logic rst,

    // Output clock
    output logic clk_out,

    // External trigger
    input logic trigger,

    // Throttle control
    input logic throttle_en,
    input logic [CntrWidth-1:0] skip_value
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(cntr_width_must_be_at_least_1_a, CntrWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic sync_trigger;
  logic clk_en;
  logic [CntrWidth-1:0] throttle_cntr_value;
  logic throttle_cntr_matches;
  logic skip_cycle;
  logic reinit_throttle_cntr;

  // Optionally synchronize the trigger signal
  if (SyncTrigger) begin : gen_sync_trigger
    assign sync_trigger = trigger;
  end else begin : gen_async_trigger
    br_gate_cdc_sync br_gate_cdc_sync_trigger (
        .clk(clk_in),
        .in (trigger),
        .out(sync_trigger)
    );
  end

  // Throttle counter
  br_counter_incr #(
      .MaxValue((2 ** CntrWidth) - 1),
      .MaxIncrement(1)
  ) br_counter_incr (
      .clk,
      .rst,
      .reinit(reinit_throttle_cntr),
      .initial_value(throttle_cntr_value),
      .incr_valid(throttle_en && sync_trigger),
      .incr(1'b1),
      .value(throttle_cntr_value),
      .value_next()
  );

  assign skip_cycle = throttle_cntr_value < skip_value;
  assign reinit_throttle_cntr = !throttle_en || !sync_trigger;
  assign clk_en = !throttle_en || !sync_trigger || !skip_cycle;

  br_gate_icg_rst br_gate_icg_rst (
      .clk_in,
      .en(clk_en),
      .rst,
      .clk_out
  );

endmodule
