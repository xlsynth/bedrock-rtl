// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Round-Robin Flow Mux Testbench

module br_flow_mux_rr_tb;
  localparam int NumFlows = 3;
  localparam int Width = 8;

  logic clk;
  logic rst;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid_unstable;
  logic [Width-1:0] pop_data_unstable;

  br_flow_mux_rr #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_transfer(input logic [NumFlows-1:0] expected_ready,
                                input logic [Width-1:0] expected_data, input string message);
    td.check((push_ready & push_valid) == expected_ready, {message, ": accepted flow"});
    td.check(pop_valid_unstable, {message, ": pop_valid"});
    td.check(pop_data_unstable == expected_data, {message, ": pop_data"});
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
    check_transfer(3'b001, 8'h10, "round-robin should initialize at flow zero");

    @(posedge clk);
    #1;
    check_transfer(3'b010, 8'h21, "round-robin should advance to flow one");

    @(negedge clk);
    push_valid[0] = 1'b0;
    pop_ready = 1'b0;
    #1;
    check_transfer(3'b000, 8'h21, "flow one data should remain selected while stalled");

    @(posedge clk);
    #1;
    check_transfer(3'b000, 8'h21, "stalled cycle should not accept flow one");
    @(negedge clk);
    pop_ready = 1'b1;
    #1;
    check_transfer(3'b010, 8'h21, "priority should hold through a stall");

    @(posedge clk);
    @(negedge clk);
    push_valid[1] = 1'b0;
    push_valid[0] = 1'b1;
    #1;
    check_transfer(3'b100, 8'h32, "round-robin should advance to flow two");

    @(posedge clk);
    @(negedge clk);
    push_valid[2] = 1'b0;
    #1;
    check_transfer(3'b001, 8'h10, "round-robin should wrap to flow zero");

    @(posedge clk);
    @(negedge clk);
    push_valid[0] = 1'b0;
    td.finish();
  end

endmodule : br_flow_mux_rr_tb
