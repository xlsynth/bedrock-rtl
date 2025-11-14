// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Ready-Valid Interface Checks (Implementation)
//
// This is an internal assertion-only module that can be reused in all
// modules with ready-valid interfaces. It uses the Bedrock-internal
// implementation check macros to ensure the valid and data signals
// conform to the ready-valid interface protocol.

`include "br_asserts_internal.svh"
`include "br_unused.svh"
`include "br_registers.svh"

// ri lint_check_off NO_OUTPUT
module br_flow_checks_valid_data_impl #(
    // The number of ready-valid flows. Must be at least 1.
    parameter int NumFlows = 1,
    // The width of the data signal. Must be at least 1.
    parameter int Width = 1,
    // If 1, cover that there is backpressure.
    // If 0, assert that there is never backpressure.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableCoverBackpressure = 1,
    // If 1, assert that valid is stable when backpressured.
    // Can only be enabled if EnableCoverBackpressure is also enabled.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertValidStability = EnableCoverBackpressure,
    // If 1, assert that data is stable when backpressured.
    // Can only be enabled if EnableAssertValidStability is also enabled.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertDataStability = EnableAssertValidStability,
    // If 1, assert that data is known (not X) whenever valid is asserted.
    // This is independent of stability checks; set to 0 to disable.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    input logic rst,
    input logic [NumFlows-1:0] valid,
    input logic [NumFlows-1:0] ready,
    input logic [NumFlows-1:0][Width-1:0] data
);

  `BR_ASSERT_STATIC(legal_assert_valid_stability_a,
                    !(EnableAssertValidStability && !EnableCoverBackpressure))
  `BR_ASSERT_STATIC(legal_assert_data_stability_a,
                    !(EnableAssertDataStability && !EnableAssertValidStability))

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_valid_a, !valid)
  end

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  if (EnableCoverBackpressure) begin : gen_backpressure_checks
    if (EnableAssertValidStability) begin : gen_valid_stability_checks
      if (EnableAssertDataStability) begin : gen_valid_data_stability_checks
        for (genvar i = 0; i < NumFlows; i++) begin : gen_valid_data_stability_per_flow
          `BR_ASSERT_IMPL(valid_data_stable_when_backpressured_a,
                          !ready[i] && valid[i] |=> valid[i] && $stable(data[i]))
        end
      end else begin : gen_valid_only_stability_checks
        for (genvar i = 0; i < NumFlows; i++) begin : gen_valid_only_stability_per_flow
          `BR_ASSERT_IMPL(valid_stable_when_backpressured_a, !ready[i] && valid[i] |=> valid[i])
        end
      end
    end else begin : gen_cover_without_stability
      for (genvar i = 0; i < NumFlows; i++) begin : gen_per_flow
        `BR_COVER_IMPL(backpressure_c, !ready[i] && valid[i])
      end
    end
  end else begin : gen_no_backpressure_checks
    for (genvar i = 0; i < NumFlows; i++) begin : gen_no_backpressure_per_flow
      `BR_ASSERT_IMPL(no_backpressure_a, valid[i] |-> ready[i])
    end
  end
  // Always assert that if valid is asserted, data is known (not X), if enabled.
  if (EnableAssertDataKnown) begin : gen_data_known_checks
    for (genvar i = 0; i < NumFlows; i++) begin : gen_data_known_per_flow
      `BR_ASSERT_IMPL(data_known_a, valid[i] |-> !$isunknown(data[i]))
    end
  end
`endif  // BR_ENABLE_IMPL_CHECKS
`endif  // BR_ASSERT_ON

  `BR_UNUSED_NAMED(all_unused, {rst, valid, ready, data})

endmodule
// ri lint_check_on NO_OUTPUT
