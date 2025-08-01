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

// Bedrock-RTL Flow Register (Combined Forward & Reverse Variant)
//
// A dataflow pipeline register that behaves like a 2-entry
// FIFO. Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// All outputs are registered, although the push_ready and pop_valid signals
// also have some internal fanout.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// The cut-through latency (minimum delay from push_valid to pop_valid) is 1 cycle.
// The backpressure latency (minimum delay from pop_ready to push_ready) is 1 cycle.
// The steady-state throughput is 1 transaction per cycle.

module br_flow_reg_both #(
    // Must be at least 1
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // The combination of a br_flow_reg_rev and br_flow_reg_fwd has the black-box behavior
  // of a 2-entry FIFO (because each of them individually behaves like a 1-entry FIFO
  // with complementary timing and latency characteristics). The reverse register is
  // instantiated upstream of the forward register to achieve the design goal of having
  // all output signals driven directly from flops. This provides for a clean timing
  // interface and allows for easy integration with other ready-valid components.

  logic             internal_valid;
  logic             internal_ready;
  logic [Width-1:0] internal_data;

  br_flow_reg_rev #(
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_reg_rev (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready(internal_ready),
      .pop_valid(internal_valid),
      .pop_data (internal_data)
  );

  br_flow_reg_fwd #(
      .Width(Width),
      // The fwd stage can still backpressure the rev stage
      // without backpressuring the input.
      .EnableCoverPushBackpressure(1),
      // The rev stage has combinational paths on valid and data, so any instability on the
      // push interface will also cause instability on the internal signals.
      // But the output of the fwd stage is guaranteed to be stable either way.
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_reg_fwd (
      .clk,
      .rst,
      .push_ready(internal_ready),
      .push_valid(internal_valid),
      .push_data (internal_data),
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_reg_both
