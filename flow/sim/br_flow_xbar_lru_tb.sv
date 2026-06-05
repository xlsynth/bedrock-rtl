// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Least-Recently-Used Flow Crossbar Testbench

module br_flow_xbar_lru_tb;
  localparam int NumPushFlows = 3;
  localparam int NumPopFlows = 2;
  localparam int Width = 8;
  localparam int DestIdWidth = $clog2(NumPopFlows);

  logic clk;
  logic rst;
  logic [NumPushFlows-1:0] push_ready;
  logic [NumPushFlows-1:0] push_valid;
  logic [NumPushFlows-1:0][Width-1:0] push_data;
  logic [NumPushFlows-1:0][DestIdWidth-1:0] push_dest_id;
  logic [NumPopFlows-1:0] pop_ready;
  logic [NumPopFlows-1:0] pop_valid;
  logic [NumPopFlows-1:0][Width-1:0] pop_data;

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_data(input logic [Width-1:0] actual, input logic [Width-1:0] expected,
                            input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got 0x%0h, expected 0x%0h", message, actual, expected);
    end
  endtask

  task automatic check_accept(input logic [NumPushFlows-1:0] expected, input string message);
    if ((push_ready & push_valid) !== expected) begin
      td.error_count++;
      $error("%s: got %0b, expected %0b", message, push_ready & push_valid, expected);
    end
  endtask

  task automatic check_pop(input logic [NumPopFlows-1:0] expected_valid, input int pop_flow,
                           input logic [Width-1:0] expected_data, input string message);
    td.check(pop_valid == expected_valid, {message, ": pop_valid"});
    check_data(pop_data[pop_flow], expected_data, {message, ": pop_data"});
  endtask

  task automatic initialize_inputs;
    push_valid = '0;
    push_data[0] = Width'(8'h10);
    push_data[1] = Width'(8'h21);
    push_data[2] = Width'(8'h32);
    push_dest_id = '0;
    pop_ready = '1;
  endtask

  task automatic check_single_route(input int push_flow, input int pop_flow);
    logic [NumPushFlows-1:0] expected_push;
    logic [ NumPopFlows-1:0] expected_pop;

    expected_push = NumPushFlows'(1 << push_flow);
    expected_pop  = NumPopFlows'(1 << pop_flow);

    @(negedge clk);
    push_valid = expected_push;
    push_dest_id[push_flow] = DestIdWidth'(pop_flow);
    #1;
    check_accept(expected_push, "single-route accept");
    check_pop(expected_pop, pop_flow, push_data[push_flow], "single-route output");

    @(posedge clk);
    @(negedge clk);
    push_valid = '0;
  endtask

  task automatic check_all_routes;
    for (int push_flow = 0; push_flow < NumPushFlows; push_flow++) begin
      for (int pop_flow = 0; pop_flow < NumPopFlows; pop_flow++) begin
        check_single_route(push_flow, pop_flow);
      end
    end
  endtask

  task automatic check_parallel_routes;
    @(negedge clk);
    push_valid = 3'b101;
    push_dest_id[0] = 1'b0;
    push_dest_id[2] = 1'b1;
    #1;
    check_accept(3'b101, "parallel-route accept");
    td.check(pop_valid == 2'b11, "parallel-route pop_valid");
    check_data(pop_data[0], push_data[0], "parallel-route pop zero data");
    check_data(pop_data[1], push_data[2], "parallel-route pop one data");

    @(posedge clk);
    @(negedge clk);
    pop_ready = 2'b01;
    #1;
    check_accept(3'b001, "independent backpressure accept");
    td.check(pop_valid == 2'b11, "independent backpressure pop_valid");
    check_data(pop_data[0], push_data[0], "independent backpressure pop zero data");
    check_data(pop_data[1], push_data[2], "independent backpressure pop one data");

    @(posedge clk);
    @(negedge clk);
    push_valid[0] = 1'b0;
    pop_ready = '1;
    #1;
    check_accept(3'b100, "release backpressure accept");
    check_pop(2'b10, 1, push_data[2], "release backpressure output");

    @(posedge clk);
    @(negedge clk);
    push_valid = '0;
  endtask

  task automatic check_contention(input logic [NumPushFlows-1:0] expected, input string message);
    check_accept(expected, {message, ": accept"});
    check_pop(2'b10, 1, push_data[$clog2(expected)], message);
  endtask

  br_flow_xbar_lru #(
      .NumPushFlows(NumPushFlows),
      .NumPopFlows(NumPopFlows),
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .push_dest_id,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  initial begin
    initialize_inputs();
    td.reset_dut();
    check_all_routes();
    check_parallel_routes();

    td.reset_dut();
    push_dest_id = '1;
    push_valid   = 3'b111;
    #1;
    check_contention(3'b001, "initial LRU contention");

    @(posedge clk);
    #1;
    check_contention(3'b010, "flow one should become least recently used");

    @(negedge clk);
    pop_ready[1] = 1'b0;
    #1;
    check_accept('0, "stalled LRU contention");
    check_pop(2'b10, 1, push_data[1], "stalled LRU output");

    @(posedge clk);
    @(negedge clk);
    pop_ready[1] = 1'b1;
    #1;
    check_contention(3'b010, "LRU priority should hold through a stall");

    @(posedge clk);
    #1;
    check_contention(3'b100, "flow two should become least recently used");

    @(posedge clk);
    #1;
    check_contention(3'b001, "flow zero should become least recently used again");

    @(posedge clk);
    @(negedge clk);
    push_valid[0] = 1'b0;
    #1;
    check_contention(3'b010, "LRU should drain flow one next");

    @(posedge clk);
    @(negedge clk);
    push_valid[1] = 1'b0;
    #1;
    check_contention(3'b100, "LRU should drain flow two last");

    @(posedge clk);
    @(negedge clk);
    push_valid[2] = 1'b0;
    td.finish();
  end

endmodule : br_flow_xbar_lru_tb
