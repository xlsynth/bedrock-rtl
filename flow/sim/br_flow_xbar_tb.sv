// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Crossbar Testbench
//
// Test plan: drive fixed, round-robin, and LRU xbars with three simultaneous
// push flows targeting two pop flows. The first cycle checks full-throughput
// routing to distinct destinations and arbitration among colliding requesters;
// the second cycle keeps the backpressured requester stable and verifies it
// drains once the earlier winners have completed.

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

    push_valid = 3'b111;
    #1;
    check_accept(fixed_push_ready, push_valid, 3'b011, "fixed xbar initial accept");
    check_accept(rr_push_ready, push_valid, 3'b011, "rr xbar initial accept");
    check_accept(lru_push_ready, push_valid, 3'b011, "lru xbar initial accept");
    td.check(fixed_pop_valid == 2'b11 && rr_pop_valid == 2'b11 && lru_pop_valid == 2'b11,
             "all xbars should drive both pop valids initially");
    check_data(fixed_pop_data[0], Width'(8'h10), "fixed xbar pop0 data");
    check_data(fixed_pop_data[1], Width'(8'h21), "fixed xbar pop1 data");
    check_data(rr_pop_data[0], Width'(8'h10), "rr xbar pop0 data");
    check_data(rr_pop_data[1], Width'(8'h21), "rr xbar pop1 data");
    check_data(lru_pop_data[0], Width'(8'h10), "lru xbar pop0 data");
    check_data(lru_pop_data[1], Width'(8'h21), "lru xbar pop1 data");

    @(posedge clk);
    #1;
    push_valid[0] = 1'b0;
    push_valid[1] = 1'b0;
    #1;
    check_accept(fixed_push_ready, push_valid, 3'b100, "fixed xbar drains collided requester");
    check_accept(rr_push_ready, push_valid, 3'b100, "rr xbar drains collided requester");
    check_accept(lru_push_ready, push_valid, 3'b100, "lru xbar drains collided requester");
    td.check(fixed_pop_valid == 2'b10 && rr_pop_valid == 2'b10 && lru_pop_valid == 2'b10,
             "all xbars should drive only pop1 on drain");
    check_data(fixed_pop_data[1], Width'(8'h32), "fixed xbar drain data");
    check_data(rr_pop_data[1], Width'(8'h32), "rr xbar drain data");
    check_data(lru_pop_data[1], Width'(8'h32), "lru xbar drain data");

    @(posedge clk);
    #1;
    push_valid[2] = 1'b0;

    td.finish();
  end

endmodule
