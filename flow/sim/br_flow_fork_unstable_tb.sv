// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Fork With Unstable Push Testbench
//
// Test plan: backpressure one fork lane, revoke and reassert the blocked push
// valid, then release backpressure and verify all lanes transfer together.

module br_flow_fork_unstable_tb;
  localparam int NumFlows = 3;

  logic                clk;
  logic                rst;
  logic                push_ready;
  logic                push_valid_unstable;
  logic [NumFlows-1:0] pop_ready;
  logic [NumFlows-1:0] pop_valid_unstable;

  br_flow_fork_unstable #(
      .NumFlows(NumFlows)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid_unstable,
      .pop_ready,
      .pop_valid_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  // Check a blocked fork cycle, including the lane that still observes valid.
  task automatic check_blocked_output(input logic [NumFlows-1:0] expected_pop_valid,
                                      input string message);
    td.check(!push_ready, {message, ": push_ready should remain low"});
    td.check(pop_valid_unstable == expected_pop_valid, {message, ": pop_valid mismatch"});
  endtask

  initial begin
    push_valid_unstable = 1'b0;
    pop_ready = '0;

    td.reset_dut();

    // Lane 0 backpressures the fork; only that lane observes the blocked valid.
    @(negedge clk);
    pop_ready = 3'b110;
    push_valid_unstable = 1'b1;
    #1;
    check_blocked_output(3'b001, "initial blocked push");

    // Valid may be revoked while push_ready is low.
    @(posedge clk);
    @(negedge clk);
    push_valid_unstable = 1'b0;
    #1;
    check_blocked_output(3'b000, "blocked valid revocation");

    // The same blocked source may reassert valid before any transfer occurs.
    @(posedge clk);
    @(negedge clk);
    push_valid_unstable = 1'b1;
    #1;
    check_blocked_output(3'b001, "blocked valid reassertion");

    // All lanes transfer together once the last downstream lane is ready.
    @(posedge clk);
    @(negedge clk);
    pop_ready = '1;
    #1;
    td.check(push_ready, "fork should accept when every pop lane is ready");
    td.check(pop_valid_unstable == '1, "every pop lane should transfer");

    @(posedge clk);
    @(negedge clk);
    push_valid_unstable = 1'b0;
    #1;
    td.check(pop_valid_unstable == '0, "fork should drain");

    td.finish();
  end

endmodule : br_flow_fork_unstable_tb
