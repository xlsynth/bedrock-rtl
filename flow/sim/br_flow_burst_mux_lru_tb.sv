// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Least-Recently-Used Flow Burst Mux Testbench

module br_flow_burst_mux_lru_tb;
  localparam int NumFlows = 3;
  localparam int Width = 8;

  logic clk;
  logic rst;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0] push_last;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid_unstable;
  logic pop_last_unstable;
  logic [Width-1:0] pop_data_unstable;

  br_flow_burst_mux_lru #(
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
      .pop_valid_unstable,
      .pop_last_unstable,
      .pop_data_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_transfer(input logic [NumFlows-1:0] expected_ready,
                                input logic [Width-1:0] expected_data, input logic expected_last,
                                input string message);
    td.check((push_ready & push_valid) == expected_ready, {message, ": accepted input"});
    td.check(pop_valid_unstable, {message, ": pop_valid"});
    td.check(pop_data_unstable == expected_data, {message, ": pop_data"});
    td.check(pop_last_unstable == expected_last, {message, ": pop_last"});
  endtask

  initial begin
    push_valid = '0;
    push_last  = '0;
    push_data  = '0;
    pop_ready  = 1'b1;
    td.reset_dut();

    push_valid[1] = 1'b1;
    push_data[1]  = 8'h41;
    #1;
    check_transfer(3'b010, 8'h41, 1'b0, "first burst beat");

    @(posedge clk);
    @(negedge clk);
    push_valid   = 3'b111;
    push_last    = 3'b111;
    push_data[0] = 8'ha0;
    push_data[1] = 8'h42;
    push_data[2] = 8'hc2;
    #1;
    check_transfer(3'b010, 8'h42, 1'b1, "owner should hold through final beat");

    pop_ready = 1'b0;
    #1;
    check_transfer(3'b000, 8'h42, 1'b1, "final beat should hold while stalled");
    @(posedge clk);
    @(negedge clk);
    pop_ready = 1'b1;
    #1;
    check_transfer(3'b010, 8'h42, 1'b1, "owner should survive stalled cycle");

    @(posedge clk);
    @(negedge clk);
    push_valid[1] = 1'b0;
    #1;
    check_transfer(3'b001, 8'ha0, 1'b1, "flow zero should be least recently used next");

    @(posedge clk);
    @(negedge clk);
    push_valid[0] = 1'b0;
    #1;
    check_transfer(3'b100, 8'hc2, 1'b1, "remaining flow should drain");

    @(posedge clk);
    @(negedge clk);
    push_valid[2] = 1'b0;
    td.finish();
  end

endmodule : br_flow_burst_mux_lru_tb
