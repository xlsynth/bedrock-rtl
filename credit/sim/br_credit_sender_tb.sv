// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

module br_credit_sender_tb;

  parameter int Width = 8;
  parameter int MaxCredit = 2;
  parameter int NumFlows = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter int NumPopValidCopies = 2;

  localparam int CounterWidth = $clog2(MaxCredit + 1);
  localparam int PopCreditWidth = $clog2(MaxCredit + 1);

  logic clk;
  logic rst;

  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0][Width-1:0] push_data;

  logic pop_sender_in_reset;
  logic [PopCreditWidth-1:0] pop_credit;
  logic [NumFlows-1:0][NumPopValidCopies-1:0] pop_valid;
  logic [NumFlows-1:0][Width-1:0] pop_data;

  logic [CounterWidth-1:0] credit_count;
  logic [CounterWidth-1:0] credit_available;

  br_credit_sender #(
      .Width(Width),
      .MaxCredit(MaxCredit),
      .NumFlows(NumFlows),
      .PopCreditMaxChange(MaxCredit),
      .RegisterPopOutputs(RegisterPopOutputs),
      .NumPopValidCopies(NumPopValidCopies),
      .EnableCoverCreditWithhold(0),
      .EnableCoverPopReceiverInReset(0)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_sender_in_reset,
      .pop_receiver_in_reset(1'b0),
      .pop_credit,
      .pop_valid,
      .pop_data,
      .credit_initial(CounterWidth'(MaxCredit)),
      .credit_withhold('0),
      .credit_count,
      .credit_available
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_pop_valid(input logic [NumFlows-1:0] expected, input string message);
    for (int i = 0; i < NumFlows; i++) begin
      for (int j = 0; j < NumPopValidCopies; j++) begin
        td.check(pop_valid[i][j] === expected[i], $sformatf(
                 "%s for flow %0d copy %0d", message, i, j));
      end
    end
  endtask

  initial begin
    push_valid = '0;
    push_data  = '0;
    pop_credit = '0;

    td.reset_dut();
    #1;

    check_pop_valid('0, "pop_valid should be low after reset");

    @(negedge clk);
    push_valid = '1;
    for (int i = 0; i < NumFlows; i++) begin
      push_data[i] = Width'(8'hd3 + i);
    end
    #1;
    td.check(push_ready == '1, "all active pushes should be ready");

    if (RegisterPopOutputs) begin
      @(negedge clk);
    end

    check_pop_valid('1, "all pop_valid copies should assert");
    for (int i = 0; i < NumFlows; i++) begin
      td.check(pop_data[i] === push_data[i], $sformatf("pop_data mismatch for flow %0d", i));
    end

    if (!RegisterPopOutputs) begin
      @(negedge clk);
    end

    push_valid = '0;

    if (RegisterPopOutputs) begin
      @(negedge clk);
    end else begin
      #1;
    end

    check_pop_valid('0, "all pop_valid copies should deassert");

    @(negedge clk);
    pop_credit = PopCreditWidth'(NumFlows);
    @(negedge clk);
    pop_credit = '0;
    #1;
    td.check_integer(credit_count, MaxCredit, "credit was not replenished");

    td.finish();
  end

endmodule
