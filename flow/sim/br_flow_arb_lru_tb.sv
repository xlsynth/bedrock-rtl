// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Least-Recently-Used Flow Arbiter Testbench

module br_flow_arb_lru_tb;
  localparam int NumFlows = 3;

  logic clk;
  logic rst;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic pop_ready;
  logic pop_valid_unstable;

  br_flow_arb_lru #(
      .NumFlows(NumFlows)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_accept(input logic [NumFlows-1:0] expected, input string message);
    if ((push_ready & push_valid) !== expected) begin
      td.error_count++;
      $error("%s: got %0b, expected %0b", message, push_ready & push_valid, expected);
    end
  endtask

  initial begin
    push_valid = '0;
    pop_ready  = 1'b1;
    td.reset_dut();

    push_valid = 3'b111;
    #1;
    check_accept(3'b001, "LRU should initialize at flow zero");

    @(posedge clk);
    #1;
    check_accept(3'b010, "flow one should become least recently used");

    @(negedge clk);
    push_valid[0] = 1'b0;
    pop_ready = 1'b0;
    #1;
    check_accept(3'b000, "backpressure should suppress acceptance");
    td.check(pop_valid_unstable, "grant should remain valid while stalled");

    @(posedge clk);
    #1;
    check_accept(3'b000, "stalled cycle should not accept a request");
    @(negedge clk);
    pop_ready = 1'b1;
    #1;
    check_accept(3'b010, "LRU state should hold through a stall");

    @(posedge clk);
    @(negedge clk);
    push_valid[1] = 1'b0;
    push_valid[0] = 1'b1;
    #1;
    check_accept(3'b100, "flow two should become least recently used");

    @(posedge clk);
    @(negedge clk);
    push_valid[2] = 1'b0;
    #1;
    check_accept(3'b001, "flow zero should become least recently used again");

    @(posedge clk);
    @(negedge clk);
    push_valid[0] = 1'b0;
    #1;
    td.check(!pop_valid_unstable, "arbiter should drain");

    td.finish();
  end

endmodule : br_flow_arb_lru_tb
