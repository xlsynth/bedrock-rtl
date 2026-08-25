// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL CDC Register
//
// Testplan:
// - Exercise independent push_clk and pop_clk domains with independently deasserting resets.
// - Check ready/valid protocol assumptions at the push and pop interfaces.
// - Check forward progress, deadlock freedom, and single-entry capacity behavior.
// - Check end-to-end ordering and payload integrity from accepted push to accepted pop.
// - Check that invalid pop_data is blocked at the br_cdc_reg boundary.
// - Check pop_valid/pop_data stability while the pop side is backpressured.
// - Cover nonzero payload transfer, push backpressure, pop backpressure, reset overlap,
//   and both registered and unregistered pop output configurations.

`include "br_asserts.svh"

module br_cdc_reg_fpv_monitor #(
    parameter int Width = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterResetActive = 1,
    parameter int NumSyncStages = 3,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableCoverPopBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPushDataKnown = 1,
    parameter bit EnableAssertFinalNotValid = 1,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    parameter bit EnableAssertNoPopBackpressure = !EnableCoverPopBackpressure
) (
    // FV system clock and reset.
    input logic clk,
    input logic rst,

    // Push-side interface.
    input logic             push_clk,
    input logic             push_rst,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface.
    input logic pop_clk,
    input logic pop_rst,
    input logic pop_ready
);

  logic             push_ready;
  logic             pop_valid;
  logic [Width-1:0] pop_data;

  br_cdc_reg #(
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableCoverPopBackpressure(EnableCoverPopBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertNoPopBackpressure(EnableAssertNoPopBackpressure)
  ) dut (
      .push_clk,
      .push_rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  logic push_vr;
  logic pop_vr;
  logic fv_rst;

  assign push_vr = push_valid && push_ready;
  assign pop_vr  = pop_valid && pop_ready;
  assign fv_rst  = push_rst || pop_rst;

  if (EnableCoverPopBackpressure) begin : gen_pop_ready_liveness
    // Prevent destination backpressure from remaining asserted indefinitely.
    `BR_ASSUME_CR(pop_ready_liveness_a, !pop_ready |-> s_eventually pop_ready, pop_clk, pop_rst)
  end

  if (EnableCoverPushBackpressure) begin : gen_push_backpressure
    if (EnableAssertPushValidStability) begin : gen_push_valid_stability
      // Hold push_valid until the CDC register accepts the transfer.
      `BR_ASSUME_CR(push_valid_stability_a, push_valid && !push_ready |=> push_valid, push_clk,
                    push_rst)
    end
    if (EnableAssertPushDataStability) begin : gen_push_data_stability
      // Hold push_data until the CDC register accepts the transfer.
      `BR_ASSUME_CR(push_data_stability_a, push_valid && !push_ready |=> $stable(push_data),
                    push_clk, push_rst)
    end
  end else if (EnableAssertNoPushBackpressure) begin : gen_no_push_backpressure
    // Keep the source legal when this configuration forbids push-side backpressure.
    `BR_ASSUME_CR(no_push_backpressure_a, push_valid |-> push_ready, push_clk, push_rst)
  end

  if (EnableCoverPopBackpressure ||
      (!EnableCoverPopBackpressure &&
       EnableAssertNoPopBackpressure)) begin : gen_push_to_pop_liveness
    if (EnableCoverPushBackpressure && EnableAssertPushValidStability) begin : gen_stable
      // Every persistent push offer eventually becomes visible at the destination.
      `BR_ASSERT_CR(push_to_pop_liveness_a, push_valid |-> s_eventually pop_valid, clk, fv_rst)
    end else begin : gen_not_stable
      // Without a persistent offer, only accepted pushes require forward progress.
      `BR_ASSERT_CR(push_to_pop_liveness_a, push_vr |-> s_eventually pop_valid, clk, fv_rst)
    end
  end

  if (!EnableCoverPopBackpressure && EnableAssertNoPopBackpressure) begin : gen_no_pop_backpressure
    // Keep the destination legal when this configuration forbids pop-side backpressure.
    `BR_ASSUME_CR(no_pop_backpressure_a, pop_ready, pop_clk, pop_rst)
  end

  if (!RegisterPopOutputs) begin : gen_unregistered_pop_output_checks
    // Unregistered outputs are directly qualified by internal_pop_valid and must be zero when invalid.
    `BR_ASSERT_CR(invalid_pop_data_blocked_a, !pop_valid |-> pop_data == '0, pop_clk, fv_rst)
  end

  // Prevent payload movement while the output remains invalid in either output mode.
  `BR_ASSERT_CR(invalid_pop_data_stability_a,
                !pop_valid && !$fell(pop_valid) |-> $stable(pop_data), pop_clk, fv_rst)

  if (EnableCoverPopBackpressure) begin : gen_pop_backpressure_stability
    // Hold valid and payload stable while the destination applies backpressure.
    `BR_ASSERT_CR(pop_backpressure_stability_a,
                  pop_valid && !pop_ready |=> pop_valid && $stable(pop_data), pop_clk, fv_rst)
  end

  // Preserve ordering and payload integrity across the asynchronous clock boundary.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0),
      .MAX_PENDING(RegisterPopOutputs ? 2 : 1)
  ) scoreboard (
      .incoming_clk(push_clk),
      .outgoing_clk(pop_clk),
      .rstN(!rst),
      .incoming_vld(push_vr),
      .incoming_data(push_data),
      .outgoing_vld(pop_vr),
      .outgoing_data(pop_data)
  );

  // Exercise a nonzero payload so invalid-data blocking is non-vacuous.
  `BR_COVER_CR(nonzero_push_c, push_vr && push_data != '0, push_clk, push_rst)

  // Exercise push-side backpressure when enabled.
  if (EnableCoverPushBackpressure) begin : gen_push_backpressure_cover
    `BR_COVER_CR(push_backpressure_c, push_valid && !push_ready, push_clk, push_rst)
  end

  // Exercise pop-side backpressure when enabled.
  if (EnableCoverPopBackpressure) begin : gen_pop_backpressure_cover
    `BR_COVER_CR(pop_backpressure_c, pop_valid && !pop_ready, pop_clk, pop_rst)
  end

  // Exercise independent reset release across the two clock domains.
  `BR_COVER(reset_overlap_c, push_rst != pop_rst)

endmodule : br_cdc_reg_fpv_monitor
