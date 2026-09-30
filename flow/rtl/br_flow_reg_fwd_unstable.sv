// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Register (Forward Variant, Unstable Push Interface)
//
// A forward flow register that accepts valid and data that may change or be
// revoked while push_ready is low, then presents a stable ready-valid pop
// interface. Only a transfer observed while push_ready is high is captured.
//
// The cut-through latency (minimum delay from push_valid_unstable to pop_valid)
// is 1 cycle. The backpressure latency (minimum delay from pop_ready to
// push_ready) is 0 cycles. The steady-state throughput is 1 transaction per
// cycle.

`include "br_asserts.svh"

module br_flow_reg_fwd_unstable #(
    // Must be at least 1
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_data_unstable is always known (not X) when
    // push_valid_unstable is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, cover that the pop side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPopBackpressure = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    // If 1, assert that pop-side backpressure is impossible.
    // Can only be enabled if EnableCoverPopBackpressure is disabled.
    parameter bit EnableAssertNoPopBackpressure = !EnableCoverPopBackpressure
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    output logic             push_ready,
    input  logic             push_valid_unstable,
    input  logic [Width-1:0] push_data_unstable,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(legal_assert_no_pop_backpressure_a,
                    !(EnableAssertNoPopBackpressure && EnableCoverPopBackpressure))
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  // Rely on submodule integration checks.

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // The forward register captures only ready/valid transfers and holds its
  // registered pop outputs during downstream backpressure. Disable its
  // push-side stability checks because instability is this wrapper's contract.
  br_flow_reg_fwd #(
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(1'b0),
      .EnableAssertPushDataStability(1'b0),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableCoverPopBackpressure(EnableCoverPopBackpressure),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertNoPopBackpressure(EnableAssertNoPopBackpressure)
  ) br_flow_reg_fwd (
      .clk,
      .rst,
      .push_ready,
      .push_valid(push_valid_unstable),
      .push_data (push_data_unstable),
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks.

endmodule : br_flow_reg_fwd_unstable
