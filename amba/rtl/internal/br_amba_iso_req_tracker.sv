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
//
// Bedrock-RTL AXI Isolation Request Tracker and Generator
//
// This module monitors the AXI request channel from upstream to downstream
// and keeps count of the number of expected responses from the downstream side.
// When the isolate_req signal is asserted, the module will begin ignoring
// requests from the upstream side (and stop forwarding responses upstream), and
// unconditionally accepting (and discarding) responses from downstream. The
// isolate_done signal is asserted to indicate that the upstream is isolated and
// may be reset.
//
// After an upstream component has been reset, the isolate_req signal may be
// deasserted. Once deasserted the module will continue to block new upstream
// requests from upstream until all expected responses have been received from
// downstream. At this point the isolate_done signal is deasserted and normal
// operation resumes (i.e. the upstream component is reconnected to the
// downstream side).

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_amba_iso_req_tracker #(
    parameter int MaxOutstanding = 128
) (
    input  logic clk,
    input  logic rst,
    // AW or AR channel from upstream
    output logic upstream_axready,
    input  logic upstream_axvalid,
    // R or B channel to upstream
    input  logic upstream_xready,
    output logic upstream_xvalid,
    output logic upstream_xlast,
    // AW or AR channel to downstream
    input  logic downstream_axready,
    output logic downstream_axvalid,
    // R or B channel to downstream
    output logic downstream_xready,
    input  logic downstream_xvalid,
    input  logic downstream_xlast,
    // Isolate request
    input  logic isolate_req,
    output logic isolate_done
);

  // Integration checks
  `BR_ASSERT_STATIC(max_outstanding_gte_1_a, MaxOutstanding > 1)
  // Check that the isolate request can only rise when isolate_done is false.
  `BR_ASSERT_INTG(legal_request_rise_a, $rose(isolate_req) |-> !isolate_done)
  // Check that the isolate request can only fall when isolate_done is true.
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(isolate_req) |-> isolate_done)

  // Local parameters
  localparam int RespCountWidth = $clog2(MaxOutstanding + 1);

  // Local signals
  logic incr_valid;
  logic decr_valid;
  logic [RespCountWidth-1:0] expected_resp_count;
  logic isolated;
  logic count_max;

  //
  // Implementation
  //

  // Counter

  // Increment counter by number of expected responses whenever a request is accepted on
  // the downstream side.
  assign incr_valid = downstream_axvalid && downstream_axready;

  // Decrement counter by 1 whenever a last response is returned from the downstream side.
  assign decr_valid = downstream_xvalid && downstream_xready && downstream_xlast;

  br_counter #(
      .MaxValue(MaxOutstanding),
      .MaxChange(1),
      .EnableWrap(0),
      .EnableSaturate(0)
  ) br_counter_exp_resp_count (
      .clk,
      .rst,
      //
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid,
      .incr(1'b1),
      .decr_valid,
      .decr(1'b1),
      .value(expected_resp_count),
      .value_next()
  );

  assign count_max = (expected_resp_count == MaxOutstanding);

  // block upstream->downstream requests when it is isolated
  assign upstream_axready = downstream_axready && !isolated && !count_max;
  assign downstream_axvalid = upstream_axvalid && !isolated && !count_max;

  // accept, but don't forward new responses when isolated
  assign upstream_xvalid = downstream_xvalid && !isolated;
  assign downstream_xready = upstream_xready || isolated;

  // pass through last signal
  assign upstream_xlast = downstream_xlast;

  // FSM
  logic isolate_done_next;
  `BR_REG(isolate_done, isolate_done_next)

  assign isolate_done_next = isolate_done ?
      // Deassert isolate_done only if isolate_req is dropped and expected_resp_count is 0.
      !(expected_resp_count == '0 && !isolate_req)
      // Assert isolate_done if isolate_req is asserted (i.e. isolate_req is handled immediately)
      : isolate_req;

  // Start blocking traffic as soon as isolate_req is asserted, and continue until
  // isolate_done is deasserted.
  assign isolated = isolate_req || isolate_done;

endmodule
