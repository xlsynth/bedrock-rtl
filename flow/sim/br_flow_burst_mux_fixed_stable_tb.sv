// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Stable Fixed-Priority Flow Burst Mux Testbench

module br_flow_burst_mux_fixed_stable_tb;
  localparam int NumFlows = 3;
  localparam int Width = 8;

  logic clk;
  logic rst;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0] push_last;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid;
  logic pop_last;
  logic [Width-1:0] pop_data;

  br_flow_burst_mux_fixed_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_last,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_last,
      .pop_data
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_output(input logic [Width-1:0] expected_data, input logic expected_last,
                              input string message);
    td.check(pop_valid, {message, ": pop_valid"});
    td.check(pop_data == expected_data, {message, ": pop_data"});
    td.check(pop_last == expected_last, {message, ": pop_last"});
  endtask

  initial begin
    push_valid = '0;
    push_last  = '0;
    push_data  = '0;
    pop_ready  = 1'b1;
    td.reset_dut();

    push_valid[1] = 1'b1;
    push_data[1]  = 8'h41;
    @(posedge clk);
    #1;
    check_output(8'h41, 1'b0, "first beat should appear after one cycle");

    @(negedge clk);
    push_valid   = 3'b111;
    push_last    = 3'b111;
    push_data[0] = 8'ha0;
    push_data[1] = 8'h42;
    push_data[2] = 8'hc2;
    @(posedge clk);
    #1;
    check_output(8'h42, 1'b1, "owner final beat should follow first beat");

    @(negedge clk);
    pop_ready = 1'b0;
    push_valid[1] = 1'b0;
    #1;
    td.check(push_ready == 3'b000, "full output should backpressure waiting flows");
    @(posedge clk);
    #1;
    check_output(8'h42, 1'b1, "final beat should hold while stalled");

    @(negedge clk);
    pop_ready = 1'b1;
    @(posedge clk);
    #1;
    check_output(8'ha0, 1'b1, "fixed priority should select flow zero next");

    @(negedge clk);
    push_valid[0] = 1'b0;
    @(posedge clk);
    #1;
    check_output(8'hc2, 1'b1, "remaining flow should drain");

    @(negedge clk);
    push_valid[2] = 1'b0;
    @(posedge clk);
    #1;
    td.check(!pop_valid, "stable burst mux should drain");
    td.finish();
  end

endmodule : br_flow_burst_mux_fixed_stable_tb
