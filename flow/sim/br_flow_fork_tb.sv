// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Fork Testbench
//
// Test plan: check the all-ready transfer case and verify that a stalled pop
// applies push-side backpressure while leaving only that pop valid.

module br_flow_fork_tb;
  parameter int NumFlows = 3;

  logic clk;
  logic rst;

  logic push_ready;
  logic push_valid;
  logic [NumFlows-1:0] pop_ready;
  logic [NumFlows-1:0] pop_valid_unstable;

  br_flow_fork #(
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

  initial begin
    push_valid = 1'b0;
    pop_ready  = '1;

    td.reset_dut();

    push_valid = 1'b1;
    #1;
    td.check(push_ready, "fork should be ready when all pops are ready");
    td.check(pop_valid_unstable == '1, "fork should assert all pop valids");

    pop_ready[1] = 1'b0;
    #1;
    td.check(!push_ready, "fork should backpressure when any pop is not ready");
    td.check(pop_valid_unstable == NumFlows'(1 << 1), "fork should only validate stalled pop");

    pop_ready = '1;
    @(posedge clk);
    #1;
    push_valid = 1'b0;

    td.finish();
  end

endmodule
