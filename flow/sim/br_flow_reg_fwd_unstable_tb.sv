// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Forward Flow Register With Unstable Push Testbench
//
// Test plan: fill the register, change and revoke the blocked push interface,
// verify that the registered pop interface stays stable, then replace the held
// item with a simultaneous pop and push.

module br_flow_reg_fwd_unstable_tb #(
    parameter int Width = 8
);
  localparam logic [Width-1:0] HeldData = '1;
  localparam logic [Width-1:0] ChangedData = '0;
  localparam logic [Width-1:0] RevokedData = Width'('ha5);
  localparam logic [Width-1:0] ReplacementData = Width'('h96);

  logic             clk;
  logic             rst;

  logic             push_ready;
  logic             push_valid_unstable;
  logic [Width-1:0] push_data_unstable;
  logic             pop_ready;
  logic             pop_valid;
  logic [Width-1:0] pop_data;

  br_flow_reg_fwd_unstable #(
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid_unstable,
      .push_data_unstable,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  br_test_driver td (
      .clk,
      .rst
  );

  // Check the valid registered pop item and detect both data mismatches and X values.
  task automatic check_pop(input logic [Width-1:0] expected_data, input string message);
    td.check(pop_valid, {message, ": pop_valid should be asserted"});
    td.check(pop_data === expected_data, {message, ": pop_data mismatch"});
  endtask

  initial begin
    if (Width < 1) begin
      $fatal(1, "Width must be at least 1");
    end

    push_valid_unstable = 1'b0;
    push_data_unstable = '0;
    pop_ready = 1'b0;

    td.reset_dut();
    #1;
    td.check(push_ready, "empty register should be ready after reset");
    td.check(!pop_valid, "empty register should not assert pop_valid after reset");

    // Capture one item while the downstream side is stalled.
    @(negedge clk);
    push_valid_unstable = 1'b1;
    push_data_unstable  = HeldData;
    #1;
    td.check(push_ready, "empty register should accept the first push");
    td.check(!pop_valid, "forward register should add one cycle of latency");

    @(posedge clk);
    #1;
    td.check(!push_ready, "full register should backpressure the push side");
    check_pop(HeldData, "captured item");

    // Valid and data may change while push_ready is low. Neither change may
    // disturb the held registered pop item.
    @(negedge clk);
    push_valid_unstable = 1'b1;
    push_data_unstable  = ChangedData;
    #1;
    td.check(!push_ready, "blocked changed push should remain unaccepted");
    check_pop(HeldData, "held item after blocked data change");

    @(posedge clk);
    #1;
    check_pop(HeldData, "held item after blocked data-change cycle");

    // Revoking valid and changing data again while blocked must also be ignored.
    @(negedge clk);
    push_valid_unstable = 1'b0;
    push_data_unstable  = RevokedData;
    #1;
    td.check(!push_ready, "blocked revoked push should remain unaccepted");
    check_pop(HeldData, "held item after blocked valid revocation");

    @(posedge clk);
    #1;
    check_pop(HeldData, "held item after blocked valid-revocation cycle");

    // Pop the held item and accept its replacement on the same edge.
    @(negedge clk);
    pop_ready = 1'b1;
    push_valid_unstable = 1'b1;
    push_data_unstable = ReplacementData;
    #1;
    td.check(push_ready, "simultaneous pop/push should make push_ready high");
    check_pop(HeldData, "item presented before simultaneous pop/push");

    @(posedge clk);
    #1;
    check_pop(ReplacementData, "replacement after simultaneous pop/push");

    // Backpressure the replacement to demonstrate that the stable pop contract
    // continues after a simultaneous transfer.
    @(negedge clk);
    pop_ready = 1'b0;
    push_valid_unstable = 1'b0;
    push_data_unstable = ChangedData;
    #1;
    td.check(!push_ready, "replacement should backpressure the push side");
    check_pop(ReplacementData, "backpressured replacement");

    @(posedge clk);
    #1;
    check_pop(ReplacementData, "held backpressured replacement");

    // Drain the final item so final-not-valid assertions can check a clean end state.
    @(negedge clk);
    pop_ready = 1'b1;
    #1;
    td.check(push_ready, "draining replacement should make push_ready high");
    check_pop(ReplacementData, "replacement before drain");

    @(posedge clk);
    #1;
    td.check(!pop_valid, "register should be empty after the final drain");

    @(negedge clk);
    pop_ready = 1'b0;
    push_data_unstable = '0;

    td.finish();
  end

endmodule : br_flow_reg_fwd_unstable_tb
