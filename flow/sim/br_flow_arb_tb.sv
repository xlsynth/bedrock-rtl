// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Arbiter Testbench
//
// Test plan: apply simultaneous stable requests to the selected flow arbiter
// with the pop side ready. Check policy-specific priority updates, priority hold
// under downstream backpressure, onehot ready behavior, and orderly drain of
// requesters.

module br_flow_arb_tb #(
    parameter int NumFlows   = 3,
    parameter int ArbVariant = 0
);
  localparam int ArbVariantFixed = 0;
  localparam int ArbVariantRr = 1;
  localparam int ArbVariantLru = 2;

  logic clk;
  logic rst;

  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic pop_ready;
  logic pop_valid_unstable;

  if (ArbVariant == ArbVariantFixed) begin : gen_fixed
    br_flow_arb_fixed #(
        .NumFlows(NumFlows)
    ) dut (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .pop_ready,
        .pop_valid_unstable
    );
  end else if (ArbVariant == ArbVariantRr) begin : gen_rr
    br_flow_arb_rr #(
        .NumFlows(NumFlows)
    ) dut (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .pop_ready,
        .pop_valid_unstable
    );
  end else begin : gen_lru
    br_flow_arb_lru #(
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

  task automatic check_ready(input logic [NumFlows-1:0] actual, input logic [NumFlows-1:0] expected,
                             input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got %0b, expected %0b", message, actual, expected);
    end
  endtask

  task automatic check_accept(input logic [NumFlows-1:0] expected, input string message);
    check_ready(push_ready & push_valid, expected, message);
  endtask

  function automatic logic [NumFlows-1:0] grant_for_flow(input int flow);
    return NumFlows'(1 << flow);
  endfunction

  function automatic logic [NumFlows-1:0] expected_contention_grant(input int rotating_flow);
    return grant_for_flow((ArbVariant == ArbVariantRr || ArbVariant == ArbVariantLru) ?
                          rotating_flow : 0);
  endfunction

  initial begin
    push_valid = '0;
    pop_ready  = 1'b1;
    td.reset_dut();

    push_valid = '1;
    #1;
    check_ready(push_ready, grant_for_flow(0), "initial grant");
    td.check(pop_valid_unstable, "arbiter should report pop_valid");

    @(posedge clk);
    #1;
    check_ready(push_ready, expected_contention_grant(1), "grant after first transfer");

    @(negedge clk);
    pop_ready = 1'b0;
    #1;
    check_ready(push_ready, '0, "arbiter should stall under downstream backpressure");
    td.check(pop_valid_unstable, "arbiter should retain pop_valid while stalled");

    @(posedge clk);
    #1;
    pop_ready = 1'b1;
    #1;
    check_ready(push_ready, expected_contention_grant(1), "grant after stalled cycle");

    @(posedge clk);
    #1;
    check_ready(push_ready, expected_contention_grant(2), "grant after second transfer");

    @(posedge clk);
    #1;
    check_ready(push_ready, grant_for_flow(0), "grant after third transfer");

    @(posedge clk);
    #1;
    push_valid[0] = 1'b0;
    #1;
    check_accept(grant_for_flow(1), "drain second grant");

    @(posedge clk);
    #1;
    push_valid[1] = 1'b0;
    #1;
    check_accept(grant_for_flow(2), "drain third grant");

    @(posedge clk);
    #1;
    push_valid[2] = 1'b0;
    #1;
    td.check(!pop_valid_unstable, "arbiter should drain");

    td.finish();
  end

endmodule : br_flow_arb_tb
