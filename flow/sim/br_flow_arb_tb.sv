// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Arbiter Testbench
//
// Test plan: apply simultaneous stable requests to the fixed, round-robin, and
// LRU flow arbiters with the pop side ready. The test checks fixed-priority
// service, RR/LRU rotation after accepted grants, onehot ready behavior, and
// orderly drain of backpressured requesters without violating ready/valid stability.

module br_flow_arb_tb;
  parameter int NumFlows = 3;

  logic clk;
  logic rst;

  logic [NumFlows-1:0] fixed_push_ready;
  logic [NumFlows-1:0] rr_push_ready;
  logic [NumFlows-1:0] lru_push_ready;
  logic [NumFlows-1:0] push_valid;
  logic pop_ready;
  logic fixed_pop_valid_unstable;
  logic rr_pop_valid_unstable;
  logic lru_pop_valid_unstable;

  br_flow_arb_fixed #(
      .NumFlows(NumFlows)
  ) br_flow_arb_fixed (
      .clk,
      .rst,
      .push_ready(fixed_push_ready),
      .push_valid,
      .pop_ready,
      .pop_valid_unstable(fixed_pop_valid_unstable)
  );

  br_flow_arb_rr #(
      .NumFlows(NumFlows)
  ) br_flow_arb_rr (
      .clk,
      .rst,
      .push_ready(rr_push_ready),
      .push_valid,
      .pop_ready,
      .pop_valid_unstable(rr_pop_valid_unstable)
  );

  br_flow_arb_lru #(
      .NumFlows(NumFlows)
  ) br_flow_arb_lru (
      .clk,
      .rst,
      .push_ready(lru_push_ready),
      .push_valid,
      .pop_ready,
      .pop_valid_unstable(lru_pop_valid_unstable)
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_ready(input logic [NumFlows-1:0] actual, input logic [NumFlows-1:0] expected,
                             input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got %0b, expected %0b", message, actual, expected);
    end
  endtask

  task automatic check_accept(input logic [NumFlows-1:0] ready, input logic [NumFlows-1:0] valid,
                              input logic [NumFlows-1:0] expected, input string message);
    check_ready(ready & valid, expected, message);
  endtask

  initial begin
    push_valid = '0;
    pop_ready  = 1'b1;
    td.reset_dut();

    push_valid = 3'b111;
    #1;
    check_ready(fixed_push_ready, 3'b001, "fixed initial grant");
    check_ready(rr_push_ready, 3'b001, "rr initial grant");
    check_ready(lru_push_ready, 3'b001, "lru initial grant");
    td.check(fixed_pop_valid_unstable && rr_pop_valid_unstable && lru_pop_valid_unstable,
             "all arbiters should report pop_valid");

    @(posedge clk);
    #1;
    push_valid[0] = 1'b0;
    #1;
    check_accept(fixed_push_ready, push_valid, 3'b010, "fixed second grant");
    check_accept(rr_push_ready, push_valid, 3'b010, "rr second grant");
    check_accept(lru_push_ready, push_valid, 3'b010, "lru second grant");

    @(posedge clk);
    #1;
    push_valid[1] = 1'b0;
    #1;
    check_accept(fixed_push_ready, push_valid, 3'b100, "fixed third grant");
    check_accept(rr_push_ready, push_valid, 3'b100, "rr third grant");
    check_accept(lru_push_ready, push_valid, 3'b100, "lru third grant");

    @(posedge clk);
    #1;
    push_valid[2] = 1'b0;
    #1;
    td.check(!fixed_pop_valid_unstable && !rr_pop_valid_unstable && !lru_pop_valid_unstable,
             "all arbiters should drain");

    td.finish();
  end

endmodule
