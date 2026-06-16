// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Valve Testbench
//
// Test plan: sweep every combination of push-valid, pop-ready, and enable
// patterns and verify that enable independently gates each flow.

module br_flow_valve_tb;
  parameter int NumFlows = 3;

  logic clk;
  logic rst;

  logic [NumFlows-1:0] en;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0] pop_ready;
  logic [NumFlows-1:0] pop_valid_unstable;

  br_flow_valve #(
      .NumFlows(NumFlows)
  ) dut (
      .clk,
      .rst,
      .en,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_pattern(input logic [NumFlows-1:0] valid, input logic [NumFlows-1:0] ready,
                               input logic [NumFlows-1:0] enable);
    @(negedge clk);
    push_valid = valid;
    pop_ready  = ready;
    en         = enable;
    #1;
    td.check(push_ready === (ready & enable), "valve push_ready mismatch");
    td.check(pop_valid_unstable === (valid & enable), "valve pop_valid_unstable mismatch");
    push_valid = '0;
    pop_ready  = '0;
    en         = '0;
  endtask

  initial begin
    push_valid = '0;
    pop_ready  = '0;
    en         = '0;

    td.reset_dut();

    for (int valid = 0; valid < (1 << NumFlows); valid++) begin
      for (int ready = 0; ready < (1 << NumFlows); ready++) begin
        for (int enable = 0; enable < (1 << NumFlows); enable++) begin
          check_pattern(NumFlows'(valid), NumFlows'(ready), NumFlows'(enable));
        end
      end
    end

    td.finish();
  end

endmodule : br_flow_valve_tb
