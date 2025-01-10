// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL Ready-Valid Interface Checks (Implementation)
//
// This is an internal assertion-only module that can be reused in all
// modules with ready-valid interfaces. It uses the Bedrock-internal
// implementation check macros to ensure the valid and data signals
// conform to the ready-valid interface protocol.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

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
    // If 0, cover that valid can be unstable.
    // Can only be enabled if EnableCoverBackpressure is also enabled.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertValidStability = EnableCoverBackpressure,
    // If 1, assert that data is stable when backpressured.
    // If 0, cover that data can be unstable.
    // Can only be enabled if EnableAssertValidStability is also enabled.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertDataStability = EnableAssertValidStability,
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
  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks  // ri lint_check_waive IFDEF_CODE
    if (EnableCoverBackpressure) begin : gen_backpressure_checks
      if (EnableAssertValidStability) begin : gen_valid_stability_checks
        // Assert that under backpressure conditions, the upstream properly
        // maintains the stability guarantee of the ready-valid protocol. That is,
        // on any given cycle, if valid is 1 and ready is 0, then assert that on
        // the following cycle valid is still 1 and data has not changed.
        if (EnableAssertDataStability) begin : gen_valid_data_stability_checks
          `BR_ASSERT_IMPL(valid_data_stable_when_backpressured_a,
                          !ready[i] && valid[i] |=> valid[i] && $stable(data[i]))
        end else begin : gen_valid_only_stability_checks
          // In some cases, the data may be expected to be unstable when
          // backpressured. For instance, at the output of a br_flow_mux_*
          // module. In this case, we still want to check that the valid
          // is stable when backpressured.
          `BR_ASSERT_IMPL(valid_stable_when_backpressured_a, !ready[i] && valid[i] |=> valid[i])
          `BR_COVER_IMPL(data_unstable_c, ##1 $past(!ready[i] && valid[i]) && !$stable(data[i]))
          // Assert that if valid is 1, then data must be known (not X).
          // This is not strictly a required integration check, because most modules
          // should still function correctly even if data is unknown (X).
          // However, under the ready-valid protocol convention where data is stable while
          // backpressured, unknown values are by definition not stable and therefore violate the
          // protocol requirement.
          `BR_ASSERT_IMPL(data_known_a, valid[i] |-> !$isunknown(data[i]))
        end
      end else begin : gen_no_valid_stability_checks
        // Cover that valid can be unstable when backpressured.
        `BR_COVER_IMPL(valid_unstable_c, ##1 $past(!ready[i] && valid[i]) && !valid[i])
      end
    end
  end
`endif  // BR_ENABLE_IMPL_CHECKS
`endif  // BR_ASSERT_ON

  `BR_UNUSED_NAMED(all_unused, {rst, valid, ready, data})
endmodule
// ri lint_check_on NO_OUTPUT
