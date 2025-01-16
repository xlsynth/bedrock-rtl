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

// Bedrock-RTL Weighted Round-Robin Arbiter
//
// In steady state, grants are issued in proportion to the weights of
// the active requestors. For example, if requestors 1, 4, and 7 are
// asserted continuously, we'd expect requestor 1 to get w1/(w1+w4+w7)
// of the grants, where
//   w1 = request_weight[1]
//   w4 = request_weight[4]
//   w7 = request_weight[7]
//
// Inside the arbiter, each requestor has a "weight accumulator". This
// accumulator is unsigned and initialized to zero. The larger the
// MaxAccumulatedWeight, the more "memory" the arbiter has. Larger
// MaxAccumulatedWeight values allow a request to be deasserted and
// then reasserted for longer without losing its share of the arbiter
// output. A larger MaxAccumulatedWeight also tends to increase the
// burstiness of the arbiter output.
//
// The high-level operation of the arbiter is:
// 1. Grant the active requestor with the largest accumulated weight
// 2. If the accumulated weight of the granted requestor is zero,
//    a. Increment all accumulated weights by the corresponding weight
//    b. Saturate the counts at the configurable maximum accumulated weight
// 3. Decrement the accumulated weight of the granted requestor by 1
//
// We could implement the above exactly, but Step 1 tends to be expensive
// and high latency. A reasonable approximation is:
// 1. Assign a 1-bit priority to each requestor
//    a. Priority = 1 if accumulated weight is non-zero else 0
// 2. Grant the active requestor with the largest priority, using RR to break ties
// 3. If the accumulated weight of the granted requestor is zero,
//    a. Increment all accumulated weights by the corresponding weight
//    b. Saturate the counts at the configurable maximum accumulated weight
// 4. Decrement the accumulated weight of the granted requestor by 1

module br_arb_weighted_rr #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    parameter int MaxWeight = 1,
    parameter int MaxAccumulatedWeight = 1,
    localparam int WeightWidth = $clog2(MaxWeight + 1),
    localparam int AccumulatedWeightWidth = $clog2(MaxAccumulatedWeight + 1)
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][WeightWidth-1:0] request_weight,
    output logic [NumRequesters-1:0] grant
);
  //------------------------------------------
  // Arbitrate, prioritizing requests with
  // non-zero accumulated weight
  //------------------------------------------

  logic [NumRequesters-1:0] request_priority;

  br_arb_pri_rr #(
      .NumRequesters(NumRequesters),
      .NumPriorities(2)
  ) br_arb_pri_rr_inst (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .request_priority,
      .grant
  );

  //------------------------------------------
  // Track per-request accumulated weight
  //------------------------------------------

  logic non_zero_weight_request;
  logic incr_accumulated_weight;
  assign non_zero_weight_request = |(request & request_priority);
  assign incr_accumulated_weight = enable_priority_update && |request && !non_zero_weight_request;

  logic [NumRequesters-1:0][AccumulatedWeightWidth-1:0] accumulated_weight;

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_accumulated_weight
    br_counter #(
        .MaxValue(MaxAccumulatedWeight),
        .MaxChange(MaxWeight),
        .EnableWrap(1)  // TODO(btowles): change this to EnableSaturation once implemented
    ) br_counter_inst (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value({AccumulatedWeightWidth{1'b0}}),
        .incr_valid(incr_accumulated_weight),
        .incr(request_weight[i]),
        .decr_valid(grant[i]),
        .decr(WeightWidth'(1'b1)),
        .value(accumulated_weight[i]),
        .value_next()
    );

    assign request_priority[i] = |accumulated_weight[i];
  end
endmodule
