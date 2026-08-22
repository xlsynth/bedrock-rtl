// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Stable Data CDC with Automatic Update
//
// Testplan:
// - Exercise independent src_clk and dst_clk domains with independently deasserting resets.
// - Model source updates only from externally visible src_data changes.
// - Check every modeled source update reaches the destination exactly once with matching data.
// - Check destination data changes only with dst_updated.
// - Check accepted updates make forward progress without assuming reset release ordering.
// - Cover source changes, nonzero transfer, and both reset-release orderings.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_stable_data_autoupdate_fpv_monitor #(
    parameter int Width = 1,
    parameter logic [Width-1:0] InitValue = '0,
    parameter bit RegisterResetActive = 1,
    parameter int NumSyncStages = 3
) (
    // FV system clock and reset.
    input logic clk,
    input logic rst,

    input logic src_clk,
    input logic src_rst,
    input logic [Width-1:0] src_data,

    input logic dst_clk,
    input logic dst_rst
);
  logic dst_updated;
  logic [Width-1:0] dst_data;
  logic [Width-1:0] fv_src_data_reg;
  logic src_vr;

  br_cdc_stable_data_autoupdate #(
      .Width(Width),
      .InitValue(InitValue),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages)
  ) dut (
      .src_clk,
      .src_rst,
      .src_data,
      .dst_clk,
      .dst_rst,
      .dst_updated,
      .dst_data
  );

  // The interface does not expose the internal ready signal, so an exact external assumption for
  // "infrequent" source changes would depend on the clock ratio. Check integrity only for a
  // changed source value that the RTL actually accepts; users must ensure src_data changes slowly
  // enough for their application.
  assign src_vr = !src_rst && (src_data != fv_src_data_reg) && dut.src_ready;
  `BR_REGLIX(fv_src_data_reg, src_data, src_vr, InitValue, src_clk, src_rst)

  // Every externally observed source update must eventually become visible at the destination.
  `BR_ASSERT_CR(src_to_dst_liveness_a, src_vr |-> s_eventually dst_updated, clk, rst)

  // Destination data must hold its last transferred value between updates.
  `BR_ASSERT_CR(dst_data_stability_a, !dst_updated && !$fell(dst_updated) |-> $stable(dst_data),
                dst_clk, dst_rst)

  // Preserve ordering and payload integrity for externally observed source updates.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0),
      .MAX_PENDING(2)
  ) scoreboard (
      .incoming_clk(src_clk),
      .outgoing_clk(dst_clk),
      .rstN(!rst),
      .incoming_vld(src_vr),
      .incoming_data(src_data),
      .outgoing_vld(dst_updated),
      .outgoing_data(dst_data)
  );

  // Exercise automatic update generation from a changed source value.
  `BR_COVER_CR(source_change_c, src_data != InitValue, src_clk, src_rst)

  // Exercise transfer of a non-reset payload.
  `BR_COVER_CR(nonzero_update_c, src_vr && src_data != InitValue, src_clk, src_rst)

  // Exercise both legal independent reset-release orderings.
  `BR_COVER(src_reset_releases_later_c, src_rst && !dst_rst)
  `BR_COVER(dst_reset_releases_later_c, !src_rst && dst_rst)

endmodule : br_cdc_stable_data_autoupdate_fpv_monitor
