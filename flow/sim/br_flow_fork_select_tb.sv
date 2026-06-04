// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Fork Select Testbench
//
// Test plan: sweep every downstream ready pattern for a plain fork, then also
// sweep every nonzero selection for a multihot-select fork.

module br_flow_fork_select_tb;
  parameter int NumFlows = 3;
  parameter bit UseSelectMultihot = 1;

  logic clk;
  logic rst;

  logic push_ready;
  logic push_valid;
  logic [NumFlows-1:0] push_select_multihot;
  logic [NumFlows-1:0] pop_ready;
  logic [NumFlows-1:0] pop_valid_unstable;

  if (UseSelectMultihot) begin : gen_select_multihot
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
  end else begin : gen_plain
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
  end

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic expected_push_ready(input logic [NumFlows-1:0] select_multihot,
                                               input logic [NumFlows-1:0] ready);
    return &(~select_multihot | ready);
  endfunction

  function automatic logic [NumFlows-1:0] expected_pop_valid(
      input logic [NumFlows-1:0] select_multihot, input logic [NumFlows-1:0] ready);
    logic [NumFlows-1:0] result;
    result = '0;
    for (int i = 0; i < NumFlows; i++) begin
      result[i] = select_multihot[i];
      for (int j = 0; j < NumFlows; j++) begin
        if (i != j) begin
          result[i] &= !select_multihot[j] || ready[j];
        end
      end
    end
    return result;
  endfunction

  task automatic check_pattern(input logic [NumFlows-1:0] select_multihot,
                               input logic [NumFlows-1:0] ready);
    @(negedge clk);
    push_valid = 1'b1;
    push_select_multihot = select_multihot;
    pop_ready = ready;
    #1;
    td.check(push_ready === expected_push_ready(select_multihot, ready),
             "fork-select push_ready mismatch");
    td.check(pop_valid_unstable === expected_pop_valid(select_multihot, ready),
             "fork-select pop_valid_unstable mismatch");
    push_valid = 1'b0;
    push_select_multihot = '0;
  endtask

  initial begin
    push_valid = 1'b0;
    push_select_multihot = '0;
    pop_ready = '0;

    td.reset_dut();

    if (UseSelectMultihot) begin
      for (int select_multihot = 1; select_multihot < (1 << NumFlows); select_multihot++) begin
        for (int ready = 0; ready < (1 << NumFlows); ready++) begin
          check_pattern(NumFlows'(select_multihot), NumFlows'(ready));
        end
      end
    end else begin
      for (int ready = 0; ready < (1 << NumFlows); ready++) begin
        check_pattern('1, NumFlows'(ready));
      end
    end

    td.finish();
  end

endmodule : br_flow_fork_select_tb
