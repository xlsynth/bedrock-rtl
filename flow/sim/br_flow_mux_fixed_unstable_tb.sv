// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Fixed-Priority Flow Mux With Unstable Push Testbench
//
// Test plan: hold the mux under pop backpressure, change data on a blocked
// valid flow, revoke that valid, and reassert another blocked flow. Then release
// backpressure and verify fixed-priority transfers still work.

module br_flow_mux_fixed_unstable_tb;
  localparam int NumFlows = 3;
  localparam int Width = 8;
  localparam logic [Width-1:0] InitialData = 8'h21;
  localparam logic [Width-1:0] ChangedData = 8'h22;
  localparam logic [Width-1:0] ReplacementData = 8'h32;
  localparam logic [Width-1:0] PreemptingData = 8'h10;

  logic                           clk;
  logic                           rst;
  logic [NumFlows-1:0]            push_ready;
  logic [NumFlows-1:0]            push_valid_unstable;
  logic [NumFlows-1:0][Width-1:0] push_data_unstable;
  logic                           pop_ready;
  logic                           pop_valid_unstable;
  logic [   Width-1:0]            pop_data_unstable;

  br_flow_mux_fixed_unstable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid_unstable,
      .push_data_unstable,
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  // Check the combinational mux output while all push flows are backpressured.
  task automatic check_blocked_output(input logic expected_valid,
                                      input logic [Width-1:0] expected_data, input string message);
    td.check(push_ready == '0, {message, ": push_ready should remain low"});
    td.check(pop_valid_unstable == expected_valid, {message, ": pop_valid mismatch"});
    if (expected_valid) begin
      td.check(pop_data_unstable === expected_data, {message, ": pop_data mismatch"});
    end
  endtask

  // Check which push flow transfers when downstream backpressure is released.
  task automatic check_transfer(input logic [NumFlows-1:0] expected_ready,
                                input logic [Width-1:0] expected_data, input string message);
    td.check((push_ready & push_valid_unstable) == expected_ready, {
             message, ": accepted flow mismatch"});
    td.check(pop_valid_unstable, {message, ": pop_valid should be asserted"});
    td.check(pop_data_unstable === expected_data, {message, ": pop_data mismatch"});
  endtask

  initial begin
    push_valid_unstable = '0;
    push_data_unstable = '0;
    pop_ready = 1'b0;

    td.reset_dut();

    // Present a lower-priority request while the pop side is stalled.
    @(negedge clk);
    push_valid_unstable[1] = 1'b1;
    push_data_unstable[1]  = InitialData;
    #1;
    check_blocked_output(1'b1, InitialData, "initial blocked request");

    // Data may change while the same valid request remains blocked.
    @(posedge clk);
    @(negedge clk);
    push_data_unstable[1] = ChangedData;
    #1;
    check_blocked_output(1'b1, ChangedData, "blocked data change");

    // Valid may be revoked while blocked; the combinational pop follows it.
    @(posedge clk);
    @(negedge clk);
    push_valid_unstable[1] = 1'b0;
    push_data_unstable[1]  = '0;
    #1;
    check_blocked_output(1'b0, '0, "blocked valid revocation");

    // A different flow may assert while blocked.
    @(posedge clk);
    @(negedge clk);
    push_valid_unstable[2] = 1'b1;
    push_data_unstable[2]  = ReplacementData;
    #1;
    check_blocked_output(1'b1, ReplacementData, "blocked replacement request");

    // A higher-priority request may preempt the visible blocked pop.
    @(posedge clk);
    @(negedge clk);
    push_valid_unstable[0] = 1'b1;
    push_data_unstable[0]  = PreemptingData;
    #1;
    check_blocked_output(1'b1, PreemptingData, "blocked priority preemption");

    // Release backpressure and drain the requests in fixed-priority order.
    @(posedge clk);
    @(negedge clk);
    pop_ready = 1'b1;
    #1;
    check_transfer(3'b001, PreemptingData, "higher-priority transfer");

    @(posedge clk);
    @(negedge clk);
    push_valid_unstable[0] = 1'b0;
    #1;
    check_transfer(3'b100, ReplacementData, "lower-priority transfer");

    @(posedge clk);
    @(negedge clk);
    push_valid_unstable[2] = 1'b0;
    #1;
    td.check(!pop_valid_unstable, "mux should drain");

    td.finish();
  end

endmodule : br_flow_mux_fixed_unstable_tb
