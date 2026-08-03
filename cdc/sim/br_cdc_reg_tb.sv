// SPDX-License-Identifier: Apache-2.0

// Testbench for br_cdc_reg

module br_cdc_reg_tb;
  parameter int Width = 8;
  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterResetActive = 1;
  parameter int NumSyncStages = 3;
  parameter int PushClockPeriodNs = 10;
  parameter int PopClockPeriodNs = 10;
  parameter int NumItems = 10;

  logic push_clk;
  logic push_rst;
  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_clk;
  logic pop_rst;
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  br_cdc_reg #(
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages)
  ) dut (
      .push_clk(push_clk),
      .push_rst(push_rst),
      .push_ready(push_ready),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_clk(pop_clk),
      .pop_rst(pop_rst),
      .pop_ready(pop_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data)
  );

  br_test_driver #(
      .ClockPeriodNs(PushClockPeriodNs),
      .ResetCycles  (14)
  ) td (
      .clk(push_clk),
      .rst(push_rst)
  );

  initial pop_clk = 1'b0;
  always #(PopClockPeriodNs / 2) pop_clk = ~pop_clk;
  always @(posedge pop_clk) pop_rst = push_rst;

  task automatic push_items();
    int timeout = 1000;

    for (int i = 0; i < NumItems; i++) begin
      push_valid = 1;
      push_data  = i;
      @(posedge push_clk);
      while (!push_ready && timeout > 0) begin
        timeout -= 1;
        @(posedge push_clk);
      end
      td.check(timeout > 0, "Timed out waiting for push ready");
      @(negedge push_clk);
    end
    push_valid = 0;
    push_data  = 0;
  endtask

  task automatic pop_items();
    int timeout = 1000;

    @(negedge pop_clk);
    pop_ready = 1;

    for (int i = 0; i < NumItems; i++) begin
      @(posedge pop_clk);
      while (!pop_valid && timeout > 0) begin
        timeout -= 1;
        @(posedge pop_clk);
      end
      td.check(timeout > 0, "Timed out waiting for pop valid");
      td.check_integer(pop_data, i, "Pop data mismatch");
    end

    @(negedge pop_clk);
    pop_ready = 0;
  endtask

  initial begin
    push_valid = 0;
    push_data  = 0;
    pop_ready  = 0;

    // Disable assertions during reset to avoid spurious assertion failures due
    // to X propagation.
    $assertoff;
    td.reset_dut();
    td.wait_cycles(2);
    $asserton;

    fork
      push_items();
      pop_items();
    join

    td.finish();
  end
endmodule : br_cdc_reg_tb
