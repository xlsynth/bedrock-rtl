// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Join Testbench
//
// Test plan: sweep every push-valid combination with and without downstream
// readiness and verify the corresponding joined flow control.

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

  function automatic logic [NumFlows-1:0] expected_push_ready(input logic [NumFlows-1:0] valid,
                                                              input logic ready);
    logic [NumFlows-1:0] result;
    for (int i = 0; i < NumFlows; i++) begin
      result[i] = ready;
      for (int j = 0; j < NumFlows; j++) begin
        if (i != j) begin
          result[i] &= valid[j];
        end
      end
    end
    return result;
  endfunction

  task automatic check_pattern(input logic [NumFlows-1:0] valid, input logic ready);
    @(negedge clk);
    push_valid = valid;
    pop_ready  = ready;
    #1;
    td.check(pop_valid === &valid, "join pop_valid mismatch");
    td.check(push_ready === expected_push_ready(valid, ready), "join push_ready mismatch");
    push_valid = '0;
    pop_ready  = 1'b0;
  endtask

  initial begin
    push_valid = '0;
    pop_ready  = 1'b0;

    td.reset_dut();

    for (int valid = 0; valid < (1 << NumFlows); valid++) begin
      check_pattern(NumFlows'(valid), 1'b0);
      check_pattern(NumFlows'(valid), 1'b1);
    end

    td.finish();
  end

endmodule : br_flow_join_tb
