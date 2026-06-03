// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Join Testbench
//
// Test plan: check the all-valid transfer case and verify that a missing push
// prevents a pop transfer while allowing that push to make progress.

module br_flow_join_tb;
  parameter int NumFlows = 3;

  logic clk;
  logic rst;

  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic pop_ready;
  logic pop_valid;

  br_flow_join #(
      .NumFlows(NumFlows)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    push_valid = '0;
    pop_ready  = 1'b1;

    td.reset_dut();

    push_valid = '1;
    #1;
    td.check(pop_valid, "join should be valid when all pushes are valid");
    td.check(push_ready == '1, "join should ready all pushes when pop is ready");

    push_valid[1] = 1'b0;
    #1;
    td.check(!pop_valid, "join should not be valid with a missing push");
    td.check(push_ready == NumFlows'(1 << 1), "join should only ready the missing push");

    push_valid = '1;
    @(posedge clk);
    #1;
    push_valid = '0;

    td.finish();
  end

endmodule
