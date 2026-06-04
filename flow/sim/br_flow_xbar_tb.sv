// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Crossbar Testbench
//
// Test plan: sweep every push-to-pop route, then drive fixed, round-robin, and
// LRU xbars with simultaneous push flows targeting one pop flow. Check
// arbitration policy state, priority hold under downstream backpressure, and
// orderly drain of colliding requesters.

module br_flow_xbar_tb;
  parameter int NumPushFlows = 3;
  parameter int NumPopFlows = 2;
  parameter int Width = 8;

  localparam int DestIdWidth = $clog2(NumPopFlows);

  logic clk;
  logic rst;

  logic [NumPushFlows-1:0] push_valid;
  logic [NumPushFlows-1:0][Width-1:0] push_data;
  logic [NumPushFlows-1:0][DestIdWidth-1:0] push_dest_id;
  logic [NumPopFlows-1:0] pop_ready;

  logic [NumPushFlows-1:0] fixed_push_ready;
  logic [NumPopFlows-1:0] fixed_pop_valid;
  logic [NumPopFlows-1:0][Width-1:0] fixed_pop_data;
  logic [NumPushFlows-1:0] rr_push_ready;
  logic [NumPopFlows-1:0] rr_pop_valid;
  logic [NumPopFlows-1:0][Width-1:0] rr_pop_data;
  logic [NumPushFlows-1:0] lru_push_ready;
  logic [NumPopFlows-1:0] lru_pop_valid;
  logic [NumPopFlows-1:0][Width-1:0] lru_pop_data;

  br_flow_xbar_fixed #(
      .NumPushFlows(NumPushFlows),
      .NumPopFlows(NumPopFlows),
      .Width(Width)
  ) br_flow_xbar_fixed (
      .clk,
      .rst,
      .push_ready(fixed_push_ready),
      .push_valid,
      .push_data,
      .push_dest_id,
      .pop_ready,
      .pop_valid (fixed_pop_valid),
      .pop_data  (fixed_pop_data)
  );

  br_flow_xbar_rr #(
      .NumPushFlows(NumPushFlows),
      .NumPopFlows(NumPopFlows),
      .Width(Width)
  ) br_flow_xbar_rr (
      .clk,
      .rst,
      .push_ready(rr_push_ready),
      .push_valid,
      .push_data,
      .push_dest_id,
      .pop_ready,
      .pop_valid (rr_pop_valid),
      .pop_data  (rr_pop_data)
  );

  br_flow_xbar_lru #(
      .NumPushFlows(NumPushFlows),
      .NumPopFlows(NumPopFlows),
      .Width(Width)
  ) br_flow_xbar_lru (
      .clk,
      .rst,
      .push_ready(lru_push_ready),
      .push_valid,
      .push_data,
      .push_dest_id,
      .pop_ready,
      .pop_valid (lru_pop_valid),
      .pop_data  (lru_pop_data)
  );

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

  task automatic check_ready(input logic [NumPushFlows-1:0] actual,
                             input logic [NumPushFlows-1:0] expected, input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got %0b, expected %0b", message, actual, expected);
    end
  endtask

  task automatic check_accept(input logic [NumPushFlows-1:0] ready,
                              input logic [NumPushFlows-1:0] valid,
                              input logic [NumPushFlows-1:0] expected, input string message);
    check_ready(ready & valid, expected, message);
  endtask

  task automatic check_pop(input logic [NumPopFlows-1:0] expected_valid, input int pop_flow,
                           input logic [Width-1:0] fixed_expected,
                           input logic [Width-1:0] rr_expected,
                           input logic [Width-1:0] lru_expected, input string message);
    td.check(fixed_pop_valid == expected_valid, {message, ": fixed pop_valid"});
    td.check(rr_pop_valid == expected_valid, {message, ": rr pop_valid"});
    td.check(lru_pop_valid == expected_valid, {message, ": lru pop_valid"});
    check_data(fixed_pop_data[pop_flow], fixed_expected, {message, ": fixed pop_data"});
    check_data(rr_pop_data[pop_flow], rr_expected, {message, ": rr pop_data"});
    check_data(lru_pop_data[pop_flow], lru_expected, {message, ": lru pop_data"});
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
    check_accept(fixed_push_ready, push_valid, expected_push, "fixed xbar single-route accept");
    check_accept(rr_push_ready, push_valid, expected_push, "rr xbar single-route accept");
    check_accept(lru_push_ready, push_valid, expected_push, "lru xbar single-route accept");
    check_pop(expected_pop, pop_flow, push_data[push_flow], push_data[push_flow],
              push_data[push_flow], "xbar single-route");

    @(posedge clk);
    @(negedge clk);
    push_valid = '0;
  endtask

  task automatic check_contention(
      input logic [NumPushFlows-1:0] fixed_expected, input logic [NumPushFlows-1:0] rr_expected,
      input logic [NumPushFlows-1:0] lru_expected, input string message);
    check_accept(fixed_push_ready, push_valid, fixed_expected, {message, ": fixed accept"});
    check_accept(rr_push_ready, push_valid, rr_expected, {message, ": rr accept"});
    check_accept(lru_push_ready, push_valid, lru_expected, {message, ": lru accept"});
    check_pop(2'b10, 1, push_data[$clog2(fixed_expected)], push_data[$clog2(rr_expected)],
              push_data[$clog2(lru_expected)], message);
  endtask

  initial begin
    push_valid = '0;
    push_data[0] = Width'(8'h10);
    push_data[1] = Width'(8'h21);
    push_data[2] = Width'(8'h32);
    push_dest_id[0] = DestIdWidth'(0);
    push_dest_id[1] = DestIdWidth'(1);
    push_dest_id[2] = DestIdWidth'(1);
    pop_ready = '1;

    td.reset_dut();

    for (int push_flow = 0; push_flow < NumPushFlows; push_flow++) begin
      for (int pop_flow = 0; pop_flow < NumPopFlows; pop_flow++) begin
        check_single_route(push_flow, pop_flow);
      end
    end

    td.reset_dut();

    push_dest_id = '1;
    push_valid   = 3'b111;
    #1;
    check_contention(3'b001, 3'b001, 3'b001, "xbar initial contention");

    @(posedge clk);
    #1;
    check_contention(3'b001, 3'b010, 3'b010, "xbar rotated contention");

    @(negedge clk);
    pop_ready[1] = 1'b0;
    #1;
    check_accept(fixed_push_ready, push_valid, '0, "fixed xbar stalled accept");
    check_accept(rr_push_ready, push_valid, '0, "rr xbar stalled accept");
    check_accept(lru_push_ready, push_valid, '0, "lru xbar stalled accept");
    check_pop(2'b10, 1, push_data[0], push_data[1], push_data[1], "xbar stalled contention");

    @(posedge clk);
    #1;
    pop_ready[1] = 1'b1;
    #1;
    check_contention(3'b001, 3'b010, 3'b010, "xbar retained stalled contention");

    @(posedge clk);
    #1;
    check_contention(3'b001, 3'b100, 3'b100, "xbar third contention grant");

    @(posedge clk);
    #1;
    check_contention(3'b001, 3'b001, 3'b001, "xbar wrapped contention grant");

    @(posedge clk);
    #1;
    push_valid[0] = 1'b0;
    #1;
    check_contention(3'b010, 3'b010, 3'b010, "xbar drain second grant");

    @(posedge clk);
    #1;
    push_valid[1] = 1'b0;
    #1;
    check_contention(3'b100, 3'b100, 3'b100, "xbar drain third grant");

    @(posedge clk);
    #1;
    push_valid[2] = 1'b0;

    td.finish();
  end

endmodule
