// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Register (Reverse Variant)
//
// A dataflow pipeline register that behaves like a 1-entry
// FIFO. Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// The push_ready output is registered, although it also has some internal fanout.
//
// The cut-through latency (minimum delay from push_valid to pop_valid) is 0 cycles.
// The backpressure latency (minimum delay from pop_ready to push_ready) is 1 cycle.
// The steady-state throughput is 1 transaction per cycle.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_flow_reg_rev #(
    // Must be at least 1
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
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
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // push_ready is registered. In this implementation it also
  // serves as meaning "empty." So therefore !push_ready means
  // "register valid" or "full."
  //
  // When the register is empty, the bypass path is active, so
  // that push_valid and push_data flow directly to pop_valid
  // and pop_data in the same cycle (0 latency). When pop_ready
  // However, when pop_ready is low, then the internal register
  // captures the data (like a 1-deep skid buffer).

  logic [Width-1:0] reg_data;

  assign pop_valid = !push_ready || push_valid;
  assign pop_data  = push_ready ? push_data : reg_data;

  `BR_REGI(push_ready, pop_ready || (push_ready && !push_valid), 1'b1)

  // No reset necessary for reg_data because !push_ready qualifies the value of reg_data.
  // And push_ready resets to 1'b1, so the unknown value of reg_data doesn't matter.
  // Data is updated if it push data is accepted but cannot be forwarded to pop.
  `BR_REGLN(reg_data, push_data, !pop_ready && push_ready && push_valid)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(1),
      // The buffer ensures that pop_valid/data is stable even if push isn't
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data (pop_data)
  );

  // This module must be ready to accept pushes out of reset.
  `BR_ASSERT_IMPL(reset_a, $fell(rst) |-> push_ready)

  // Check that the datapath has 0 cycle cut-through delay.
  `BR_ASSERT_IMPL(cutthrough_0_delay_a,
                  push_ready && push_valid && pop_ready |-> pop_valid && pop_data == push_data)

  // Check that that the backpressure path has 1 cycle delay.
  `BR_ASSERT_IMPL(backpressure_1_delay_a, pop_ready |=> push_ready)

endmodule : br_flow_reg_rev
