// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Stable Fixed-Priority Flow Mux Testbench

module br_flow_mux_fixed_stable_tb;
  localparam int NumFlows = 3;
  localparam int Width = 8;

  logic clk;
  logic rst;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  br_flow_mux_fixed_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_output(input logic [Width-1:0] expected_data, input string message);
    td.check(pop_valid, {message, ": pop_valid"});
    td.check(pop_data == expected_data, {message, ": pop_data"});
  endtask

  initial begin
    push_valid   = '0;
    push_data[0] = 8'h10;
    push_data[1] = 8'h21;
    push_data[2] = 8'h32;
    pop_ready    = 1'b1;
    td.reset_dut();

    push_valid = 3'b111;
    #1;
    td.check(push_ready == 3'b001, "fixed priority should select flow zero");

    @(posedge clk);
    #1;
    check_output(8'h10, "flow zero should appear after one cycle");

    @(negedge clk);
    push_valid[0] = 1'b0;
    pop_ready = 1'b0;
    #1;
    td.check(push_ready == 3'b000, "full output should backpressure inputs");

    @(posedge clk);
    #1;
    check_output(8'h10, "registered output should hold while stalled");

    @(negedge clk);
    pop_ready = 1'b1;
    @(posedge clk);
    #1;
    check_output(8'h21, "flow one should follow after flow zero drains");

    @(negedge clk);
    push_valid[1] = 1'b0;
    @(posedge clk);
    #1;
    check_output(8'h32, "flow two should follow after flow one drains");

    @(negedge clk);
    push_valid[2] = 1'b0;
    @(posedge clk);
    #1;
    td.check(!pop_valid, "stable mux should drain");
    td.finish();
  end

endmodule : br_flow_mux_fixed_stable_tb
