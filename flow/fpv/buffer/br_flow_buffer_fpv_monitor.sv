// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Buffer FPV monitor
//
// Testplan:
// - Parameter legality: cover the supported br_flow_buffer implementation modes:
//   combinational pass-through at Depth=0, flow-register composition at Depth=1
//   and Depth=2, and bypass FIFO composition at Depth>=3 with registered push
//   outputs.
// - Input assumptions: downstream ready eventually returns; when enabled, upstream
//   valid and data remain stable while the buffer backpressures push traffic.
// - Stability checks: when enabled, pop_valid and pop_data remain stable while
//   downstream backpressure is applied.
// - Ordering/data integrity: every accepted push transfer is observed in order on
//   the pop side with the same data.
// - Progress: accepted push traffic eventually makes pop_valid visible.
// - Covers: exercise push-side backpressure when that coverage is enabled.

`include "br_asserts.svh"

module br_flow_buffer_fpv_monitor #(
    parameter int Depth = 1,
    parameter int Width = 1,
    parameter bit RegisterPushOutputs = (Depth > 1),
    parameter bit RegisterPopOutputs = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPushDataKnown = 1,
    parameter bit EnableAssertFinalNotValid = 1,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input logic clk,
    input logic rst,

    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data
);
  localparam int MaxPending = (Depth < 1) ? 1 : Depth;

  // Downstream fairness is needed so progress properties are not blocked forever by the environment.
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))

  if (EnableAssertPushValidStability) begin : gen_push_valid
    // Ready/valid sources must hold valid until the transfer is accepted.
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)

    // The buffer must hold pop_valid stable while downstream applies backpressure.
    `BR_ASSERT(pop_valid_stable_a, pop_valid && !pop_ready |=> pop_valid)
  end

  if (EnableAssertPushDataStability) begin : gen_pop_data
    // Ready/valid sources must hold payload stable until the transfer is accepted.
    `BR_ASSUME(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data))

    // The buffer must hold pop_data stable while downstream applies backpressure.
    `BR_ASSERT(pop_data_stable_a, pop_valid && !pop_ready |=> $stable(pop_data))
  end

  // Accepted push data must emerge from the pop side in order and without corruption.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPending)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid & push_ready),
      .incoming_data(push_data),
      .outgoing_vld(pop_valid & pop_ready),
      .outgoing_data(pop_data)
  );

  // Presented input traffic should eventually become visible at the output.
  `BR_ASSERT(pop_forward_progress_a, push_valid |-> s_eventually (pop_valid))

  if (EnableCoverPushBackpressure) begin : gen_backpressure_cover
    // Exercise the buffer's ability to backpressure the upstream source.
    `BR_COVER(push_backpressure_c, push_valid && !push_ready)
  end

endmodule : br_flow_buffer_fpv_monitor

bind br_flow_buffer br_flow_buffer_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .RegisterPushOutputs(RegisterPushOutputs),
    .RegisterPopOutputs(RegisterPopOutputs),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
) monitor (.*);
