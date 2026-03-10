// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Stable Data CDC Unit Test
//

module br_cdc_stable_data_autoupdate_tb;
  parameter int Width = 8;
  parameter logic [Width-1:0] InitValue = '0;
  parameter bit RegisterResetActive = 1;
  parameter int NumSyncStages = 3;
  parameter int SrcClkPeriodNs = 10;
  parameter int DstClkPeriodNs = 10;

  logic src_clk;
  logic src_rst;
  logic [Width-1:0] src_data;
  logic dst_clk;
  logic dst_rst;
  logic dst_updated;
  logic [Width-1:0] dst_data;

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

  br_test_driver #(
      .ResetCycles(14)
  ) td (
      .clk(src_clk),
      .rst(src_rst)
  );

  initial dst_clk = 1'b0;
  always #(DstClkPeriodNs / 2) dst_clk = ~dst_clk;

  initial begin
    dst_rst  = 1'b1;
    src_data = InitValue;

    td.reset_dut();

    @(negedge dst_clk);
    dst_rst = 1'b0;

    @(posedge dst_clk);
    td.check_integer(dst_data, InitValue, "dst_data initial value mismatch");

    for (int i = 5; i < 15; i++) begin
      // Send the update
      @(negedge src_clk);
      src_data = i;

      // Wait until we see the update on the destination side
      @(posedge dst_clk);
      while (!dst_updated) @(posedge dst_clk);
      td.check_integer(dst_data, i, "dst_data value mismatch");
      // The data should remain stable after update
      @(posedge dst_clk);
      td.check_integer(dst_data, i, "dst_data value not stable");

      // Need to wait some cycles for the source side to be ready again
      td.wait_cycles(10);
    end

    td.finish();
  end

endmodule
