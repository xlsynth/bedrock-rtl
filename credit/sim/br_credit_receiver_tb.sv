// SPDX-License-Identifier: Apache-2.0

module br_credit_receiver_tb;

  parameter int Width = 8;
  parameter int MaxCredit = 1;
  parameter bit RegisterPushOutputs = 0;
  parameter int PopCreditMaxChange = 1;
  parameter int MaxRandomDelay = 10;

  localparam int PopCreditChangeWidth = $clog2(PopCreditMaxChange + 1);
  localparam int CounterWidth = $clog2(MaxCredit + 1);

  logic clk;
  logic rst;
  logic push_credit_stall;
  logic push_credit;
  logic push_valid;
  logic [Width-1:0] push_data;

  logic [PopCreditChangeWidth-1:0] pop_credit;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  logic [CounterWidth-1:0] credit_count;
  logic [CounterWidth-1:0] credit_available;
  logic [CounterWidth-1:0] credit_initial;
  logic [CounterWidth-1:0] credit_withhold;

  br_credit_receiver #(
      .Width(Width),
      .MaxCredit(MaxCredit),
      .RegisterPushOutputs(RegisterPushOutputs),
      .PopCreditMaxChange(PopCreditMaxChange)
  ) dut (
      .clk,
      .rst,
      .push_sender_in_reset  (1'b0),
      .push_receiver_in_reset(),
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .pop_credit,
      .pop_valid,
      .pop_data,
      .credit_count,
      .credit_available,
      .credit_initial,
      .credit_withhold
  );

  br_test_driver td (
      .clk,
      .rst
  );

  // Send credit tracking.
  // Need to keep this count to make sure we don't send push_valid when there should
  // be no credit available.
  logic [CounterWidth-1:0] send_credits;
  // Need to keep this count to make sure we don't send pop_credit when no
  // credits have been used.
  logic [CounterWidth-1:0] recv_credits;

  always_ff @(posedge clk) begin
    if (rst) begin
      send_credits <= '0;
      recv_credits <= '0;
    end else begin
      send_credits <= (send_credits + push_credit) - push_valid;
      recv_credits <= (recv_credits + pop_valid) - pop_credit;
    end
  end

  // If push credit is registered, it will take 1 cycle for push credit to come out.
  // If push credit is not registered, the credit decrement is delayed by 1 cycle.
  localparam int InitCreditDelay = 1;

  task automatic random_push(int num_pushes, int max_delay = 0);
    int delay;
    for (int i = 0; i < num_pushes; i++) begin
      @(negedge clk);
      delay = $urandom_range(0, max_delay);
      // Wait for delay to expire and send credit to become available.
      while (delay > 0 && send_credits == '0) begin
        push_valid = 0;
        @(negedge clk);
        if (delay > 0) delay--;
      end
      push_valid = 1;
      push_data  = $urandom_range(0, (2 ** Width) - 1);
      @(posedge clk);
      td.check(pop_valid, "pop_valid not asserted when push_valid is asserted");
      td.check_integer(pop_data, push_data, "pop_data does not match push_data");
    end
    @(negedge clk);
    push_valid = 0;
  endtask

  task automatic random_pop(int num_pops, int max_delay = 0);
    int delay;
    int pop_credit_next;
    int pops_left;

    pops_left = num_pops;

    while (pops_left > 0) begin
      delay = $urandom_range(0, max_delay);
      pop_credit_next = $urandom_range(1, PopCreditMaxChange);
      if (pop_credit_next > pops_left) begin
        pop_credit_next = pops_left;
      end
      if (pop_credit_next > recv_credits) begin
        pop_credit_next = recv_credits;
      end
      while (delay > '0 && credit_count > (MaxCredit - pop_credit_next)) begin
        pop_credit = 0;
        @(negedge clk);
        if (delay > 0) delay--;
      end
      pop_credit = pop_credit_next;
      pops_left  = pops_left - pop_credit_next;
      @(negedge clk);
    end

    pop_credit = 0;
  endtask

  initial begin
    int timeout;

    push_credit_stall = 0;
    push_valid = 0;
    push_data = 0;
    pop_credit = 0;
    credit_initial = $urandom_range(PopCreditMaxChange, MaxCredit);
    credit_withhold = 0;

    td.reset_dut();

    $display("Check initial credit return");
    td.wait_cycles(InitCreditDelay + MaxCredit);

    @(posedge clk);
    td.check_integer(send_credits, credit_initial, "Incorrect initial credits");

    $display("Consume all credits and check credit count");
    random_push(credit_initial);

    @(negedge clk);
    push_valid = 0;

    td.check_integer(credit_count, 0, "credit_count is not 0");
    td.check_integer(credit_available, 0, "credit_available is not 0");

    $display("Return PopCreditMaxChange credits");
    pop_credit = PopCreditMaxChange;
    td.wait_cycles(1);
    pop_credit = 0;

    td.wait_cycles(PopCreditMaxChange);
    td.check_integer(send_credits, PopCreditMaxChange, "Incorrect number of credits returned");

    $display("Simultaneous push_valid and pop_credit");
    fork
      random_push(MaxCredit, MaxRandomDelay);
      random_pop(MaxCredit, MaxRandomDelay);
    join

    td.wait_cycles(MaxRandomDelay);
    td.check_integer(send_credits, PopCreditMaxChange,
                     "Incorrect number of credits at end of test");

    td.finish();
  end

endmodule
