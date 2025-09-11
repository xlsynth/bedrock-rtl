// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_flow_reg_none #(
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
    input logic rst,

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
  logic pushed;
  assign pushed = push_valid && push_ready;

  // Push to a 1-deep buffer when backpressured while empty, or when running full
  logic buf_pushed, buf_popped;
  logic buf_valid, buf_valid_next;

  assign buf_pushed = pushed && (!pop_ready || buf_valid);
  assign buf_popped = pop_ready && buf_valid;

  assign buf_valid_next = buf_pushed || (buf_valid && !buf_popped);
  // Buffer valid is reset to 0
  `BR_REG(buf_valid, buf_valid_next)

  logic [Width-1:0] buf_data;
  // Buffer data is not reset, qualified by buf_valid
  `BR_REGLN(buf_data, push_data, buf_pushed)

  assign push_ready = pop_ready || !buf_valid;
  assign pop_valid  = push_valid || buf_valid;
  assign pop_data   = buf_valid ? buf_data : push_data;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(1),
      // Buffer stages ensure that pop_valid/data is stable even if push isn't
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

  // Check that the valid path is combinational (0 delay).
  `BR_ASSERT_IMPL(valid_propagates_with_0_delay_a, push_valid |-> pop_valid)

  // Check that that the ready path is combinational (0 delay).
  `BR_ASSERT_IMPL(backpressure_0_delay_a, pop_ready |-> push_ready)

  // Check we have expected delay for the three push cases
  `BR_ASSERT_IMPL(
      cuthrough_push_has_0_delay_a,
      (push_valid && push_ready && pop_ready && !buf_valid) |-> pop_valid && pop_data == push_data)

  `BR_ASSERT_IMPL(
      pipelined_push_has_1_delay_a,
      (push_valid && push_ready && pop_ready && buf_valid) |=> pop_valid && pop_data == $past
      (push_data))

  `BR_ASSERT_IMPL(backpressured_push_has_1_delay_a,
                  (push_valid && push_ready && !pop_ready) |=> pop_valid && pop_data == $past
                  (push_data))

  // Check buffer state is always passed to the pop interface when valid
  `BR_ASSERT_IMPL(buffer_valid_means_pop_matches_buffer_a,
                  buf_valid |-> pop_valid && pop_data == buf_data)

  // Check buffer state is cleared when popped and not pushed
  `BR_ASSERT_IMPL(buffer_cleared_when_popped_and_not_pushed_a,
                  pop_valid && pop_ready && !push_valid |=> !buf_valid)

endmodule
