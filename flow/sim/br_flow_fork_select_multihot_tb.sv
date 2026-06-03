// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Fork With Multihot Select Testbench
//
// Test plan: check multihot routing and verify that a selected stalled pop
// applies push-side backpressure while unselected pops do not participate.

module br_flow_fork_select_multihot_tb;
  parameter int NumFlows = 3;

  localparam logic [NumFlows-1:0] SelectedFlows = NumFlows'(5);

  logic clk;
  logic rst;

  logic push_ready;
  logic push_valid;
  logic [NumFlows-1:0] push_select_multihot;
  logic [NumFlows-1:0] pop_ready;
  logic [NumFlows-1:0] pop_valid_unstable;

  br_flow_fork_select_multihot #(
      .NumFlows(NumFlows)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_select_multihot,
      .pop_ready,
      .pop_valid_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    push_valid = 1'b0;
    push_select_multihot = '0;
    pop_ready = '1;

    td.reset_dut();

    push_valid = 1'b1;
    push_select_multihot = SelectedFlows;
    #1;
    td.check(push_ready, "multihot fork should be ready when selected pops are ready");
    td.check(pop_valid_unstable == SelectedFlows, "multihot fork selected valids mismatch");

    pop_ready[2] = 1'b0;
    #1;
    td.check(!push_ready, "multihot fork should backpressure on a selected stalled pop");
    td.check(pop_valid_unstable == NumFlows'(1 << 2), "multihot fork stalled valid mismatch");

    pop_ready = '1;
    @(posedge clk);
    #1;
    push_valid = 1'b0;

    td.finish();
  end

endmodule
