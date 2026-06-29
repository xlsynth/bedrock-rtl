// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

/*
 * Testbench skeleton for br_credit_counter. The DUT tracks a bounded credit
 * pool with independent increment/decrement inputs, dynamic credit withholding,
 * and decr_ready backpressure to prevent underflow.
 *
 * Planned scenarios:
 * - Reset behavior for multiple initial_value settings.
 * - Idle/no-op behavior with no increment or decrement activity.
 * - Increment-only traffic, including maximum and optional zero increments.
 * - Decrement-only traffic, including maximum and optional zero decrements.
 * - Simultaneous increment/decrement traffic with equal and unequal amounts.
 * - Dynamic withhold behavior and available-credit clipping at zero.
 * - Decrement backpressure when decr exceeds available credit.
 * - Legal no-backpressure traffic for parameter sets that assert no decrement backpressure.
 * - Bounded pseudo-random legal increment/decrement/withhold traffic.
 */
module br_credit_counter_tb;

  // Parameters
  parameter int MaxValueWidth = 8;
  parameter int MaxChangeWidth = 4;
  parameter logic [MaxValueWidth-1:0] MaxValue = 7;
  parameter logic [MaxChangeWidth-1:0] MaxChange = 3;
  parameter logic [MaxChangeWidth-1:0] MaxIncrement = MaxChange;
  parameter logic [MaxChangeWidth-1:0] MaxDecrement = MaxChange;
  parameter bit EnableCoverZeroIncrement = 1;
  parameter bit EnableCoverZeroDecrement = MaxDecrement > 1;
  parameter bit EnableCoverDecrementBackpressure = 1;
  parameter bit EnableCoverWithhold = 1;
  parameter bit EnableAssertAlwaysDecr = 0;
  parameter bit EnableAssertFinalNotValid = 1;
  parameter logic [MaxValueWidth-1:0] CoverMaxValue = MaxValue;
  parameter bit EnableAssertFinalMaxValue = 0;
  parameter bit EnableAssertFinalMinValue = 0;
  parameter bit EnableAssertNoDecrementBackpressure = 0;
  parameter int NumRandomCycles = 120;

  localparam int MaxValueP1Width = MaxValueWidth + 1;
  localparam int MaxChangeP1Width = MaxChangeWidth + 1;
  localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1);
  localparam int ChangeWidth = $clog2(MaxChangeP1Width'(MaxChange) + 1);
  localparam int TimeoutCycles = 2000;

  // Clock and Reset
  logic clk;  // Testbench clock driven by br_test_driver.
  logic rst;  // Synchronous active-high reset driven by br_test_driver.

  // Increment interface.
  logic incr_valid;  // Valid bit for the requested credit increment.
  logic [ChangeWidth-1:0] incr;  // Requested increment amount.

  // Decrement interface.
  logic decr_ready;  // DUT acceptance indication for the requested decrement.
  logic decr_valid;  // Valid bit for the requested credit decrement.
  logic [ChangeWidth-1:0] decr;  // Requested decrement amount.

  // Dynamic credit configuration.
  logic [ValueWidth-1:0] initial_value;  // Counter value loaded when reset is released.
  logic [ValueWidth-1:0] withhold;  // Credits withheld from available-credit reporting.

  // Counter outputs.
  logic [ValueWidth-1:0] value;  // Registered credit-counter state.
  logic [ValueWidth-1:0] available;  // Available credit after same-cycle increment and withhold.

  // Reference model and monitor state.
  logic [ValueWidth-1:0] expected_value;  // Scoreboard model of the registered counter value.
  logic [ValueWidth-1:0] expected_available;  // Scoreboard model of available credit.
  logic expected_decr_ready;  // Scoreboard model of decrement acceptance for the sampled cycle.
  logic sampled_incr_fire;  // Sticky sample of increment activity for the most recent cycle.
  // Sticky sample of accepted decrement activity for the most recent cycle.
  logic sampled_decr_fire;
  logic saw_zero_increment;  // Sticky observation of an enabled zero-increment scenario.
  logic saw_zero_decrement;  // Sticky observation of an enabled zero-decrement scenario.
  logic saw_max_increment;  // Sticky observation of a maximum legal increment request.
  logic saw_max_decrement;  // Sticky observation of a maximum legal decrement request.
  logic saw_decrement_backpressure;  // Sticky observation of decr_valid with decr_ready deasserted.
  logic saw_withhold;  // Sticky observation of nonzero withhold.
  // Sticky observation of concurrent increment/decrement traffic.
  logic saw_simultaneous_incr_decr;
  logic saw_value_zero;  // Sticky observation of the counter reaching zero.
  logic saw_value_max;  // Sticky observation of the counter reaching CoverMaxValue.

  br_credit_counter #(
      .MaxValueWidth(MaxValueWidth),
      .MaxChangeWidth(MaxChangeWidth),
      .MaxValue(MaxValue),
      .MaxChange(MaxChange),
      .MaxIncrement(MaxIncrement),
      .MaxDecrement(MaxDecrement),
      .EnableCoverZeroIncrement(EnableCoverZeroIncrement),
      .EnableCoverZeroDecrement(EnableCoverZeroDecrement),
      .EnableCoverDecrementBackpressure(EnableCoverDecrementBackpressure),
      .EnableCoverWithhold(EnableCoverWithhold),
      .EnableAssertAlwaysDecr(EnableAssertAlwaysDecr),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .CoverMaxValue(CoverMaxValue),
      .EnableAssertFinalMaxValue(EnableAssertFinalMaxValue),
      .EnableAssertFinalMinValue(EnableAssertFinalMinValue),
      .EnableAssertNoDecrementBackpressure(EnableAssertNoDecrementBackpressure)
  ) dut (
      .clk,
      .rst,
      .incr_valid,
      .incr,
      .decr_ready,
      .decr_valid,
      .decr,
      .initial_value,
      .withhold,
      .value,
      .available
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [ValueWidth-1:0] get_increment_amount(
      input logic valid, input logic [ChangeWidth-1:0] amount);
    // Intent: Return the effective increment contribution for one sampled cycle.
    get_increment_amount = valid ? ValueWidth'(amount) : '0;
  endfunction

  function automatic logic [ValueWidth-1:0] get_decrement_amount(
      input logic valid, input logic ready, input logic [ChangeWidth-1:0] amount);
    // Intent: Return the effective decrement contribution for one sampled cycle.
    get_decrement_amount = valid && ready ? ValueWidth'(amount) : '0;
  endfunction

  function automatic logic [ValueWidth-1:0] get_available(
      input logic [ValueWidth-1:0] model_value, input logic incr_valid_value,
      input logic [ChangeWidth-1:0] incr_value, input logic [ValueWidth-1:0] withhold_value);
    // Intent: Return the reference available-credit value including increment and withhold.
    logic [ValueWidth-1:0] value_plus_incr;  // Reference value plus same-cycle increment.

    value_plus_incr = model_value + get_increment_amount(incr_valid_value, incr_value);
    get_available   = value_plus_incr > withhold_value ? value_plus_incr - withhold_value : '0;
  endfunction

  function automatic logic get_decr_ready(
      input logic [ValueWidth-1:0] model_value, input logic incr_valid_value,
      input logic [ChangeWidth-1:0] incr_value, input logic [ValueWidth-1:0] available_value,
      input logic decr_valid_value, input logic [ChangeWidth-1:0] decr_value);
    // Intent: Return whether the current decrement request should be accepted.
    if (MaxDecrement == 1) begin
      if (EnableCoverWithhold) begin
        get_decr_ready = available_value > '0;
      end else if (EnableCoverZeroIncrement) begin
        get_decr_ready = (model_value != '0) || (incr_valid_value && (incr_value != '0));
      end else begin
        get_decr_ready = (model_value != '0) || incr_valid_value;
      end
    end else begin
      get_decr_ready = ValueWidth'(decr_valid_value ? decr_value : '0) <= available_value;
    end
  endfunction

  function automatic logic [ValueWidth-1:0] get_next_value(
      input logic [ValueWidth-1:0] model_value, input logic incr_valid_value,
      input logic [ChangeWidth-1:0] incr_value, input logic decr_valid_value,
      input logic decr_ready_value, input logic [ChangeWidth-1:0] decr_value);
    // Intent: Return the next reference counter value after accepted activity.
    get_next_value = model_value + get_increment_amount(incr_valid_value, incr_value) -
        get_decrement_amount(decr_valid_value, decr_ready_value, decr_value);
  endfunction

  task automatic init_interfaces();
    // Intent: Drive increment, decrement, initial_value, and withhold inputs to legal idle values.
    incr_valid    = 1'b0;
    incr          = '0;
    decr_valid    = 1'b0;
    decr          = '0;
    initial_value = '0;
    withhold      = '0;
  endtask

  task automatic reset_scoreboard();
    // Intent: Initialize the reference model and clear sticky monitor observations.
    expected_value = initial_value;
    expected_available = get_available(initial_value, 1'b0, '0, withhold);
    expected_decr_ready = get_decr_ready(initial_value, 1'b0, '0, expected_available, 1'b0, '0);
    sampled_incr_fire = 1'b0;
    sampled_decr_fire = 1'b0;
    saw_zero_increment = 1'b0;
    saw_zero_decrement = 1'b0;
    saw_max_increment = 1'b0;
    saw_max_decrement = 1'b0;
    saw_decrement_backpressure = 1'b0;
    saw_withhold = 1'b0;
    saw_simultaneous_incr_decr = 1'b0;
    saw_value_zero = initial_value == '0;
    saw_value_max = initial_value == ValueWidth'(CoverMaxValue);
  endtask

  task automatic timeout(input int cycles, input string message);
    // Intent: Guard a concurrent operation with a bounded simulation-time error.
    td.wait_cycles(cycles);
    td.check(1'b0, message);
  endtask

  task automatic configure_initial_value(input logic [ValueWidth-1:0] next_initial_value);
    // Intent: Set the reset-time initial_value before the next DUT reset.
    initial_value = next_initial_value;
  endtask

  task automatic set_withhold(input logic [ValueWidth-1:0] next_withhold);
    // Intent: Drive dynamic withhold independently from increment and decrement stimulus.
    withhold = next_withhold;
  endtask

  task automatic drive_increment(input logic next_incr_valid,
                                 input logic [ChangeWidth-1:0] next_incr);
    // Intent: Drive one cycle of increment-side stimulus.
    incr_valid = next_incr_valid;
    incr = next_incr;
  endtask

  task automatic drive_decrement(input logic next_decr_valid,
                                 input logic [ChangeWidth-1:0] next_decr);
    // Intent: Drive one cycle of decrement-side stimulus.
    decr_valid = next_decr_valid;
    decr = next_decr;
  endtask

  task automatic drive_cycle(input logic next_incr_valid, input logic [ChangeWidth-1:0] next_incr,
                             input logic next_decr_valid, input logic [ChangeWidth-1:0] next_decr,
                             input logic [ValueWidth-1:0] next_withhold);
    // Intent: Drive one combined cycle using independent increment/decrement BFMs.
    @(negedge clk);
    set_withhold(next_withhold);
    fork
      drive_increment(next_incr_valid, next_incr);
      drive_decrement(next_decr_valid, next_decr);
    join
    td.wait_cycles();
  endtask

  task automatic wait_idle_cycles(input int cycles);
    // Intent: Advance with increment/decrement idle while preserving configured withhold.
    for (int i = 0; i < cycles; i++) begin
      drive_cycle(1'b0, '0, 1'b0, '0, withhold);
    end
  endtask

  task automatic monitor_credit_counter();
    // Intent: Sample DUT activity, update sticky observations, and update/check the model.
    expected_available = get_available(expected_value, incr_valid, incr, withhold);
    expected_decr_ready =
        get_decr_ready(expected_value, incr_valid, incr, expected_available, decr_valid, decr);

    td.check(available === expected_available, "available mismatch");
    td.check(decr_ready === expected_decr_ready, "decr_ready mismatch");

    sampled_incr_fire = incr_valid;
    sampled_decr_fire = decr_valid && expected_decr_ready;
    saw_zero_increment |= incr_valid && (incr == '0);
    saw_zero_decrement |= decr_valid && (decr == '0);
    saw_max_increment |= incr_valid && (incr == ChangeWidth'(MaxIncrement));
    saw_max_decrement |= decr_valid && (decr == ChangeWidth'(MaxDecrement));
    saw_decrement_backpressure |= decr_valid && !expected_decr_ready;
    saw_withhold |= withhold != '0;
    saw_simultaneous_incr_decr |= incr_valid && decr_valid;

    expected_value =
        get_next_value(expected_value, incr_valid, incr, decr_valid, expected_decr_ready, decr);
    saw_value_zero |= expected_value == '0;
    saw_value_max |= expected_value == ValueWidth'(CoverMaxValue);
  endtask

  task automatic monitor_enable();
    // Intent: Run the credit-counter monitor while the test sequence is active.
    forever begin
      @(posedge clk);
      if (!rst) begin
        monitor_credit_counter();
      end

      @(negedge clk);
      if (!rst) begin
        td.check(value === expected_value, "value mismatch");
      end
    end
  endtask

  task automatic test_reset_initial_value();
    // Intent: Verify reset loads the configured initial_value across representative values.
    $display("Running test_reset_initial_value");
    init_interfaces();
    configure_initial_value('0);
    td.reset_dut();
    reset_scoreboard();
    wait_idle_cycles(2);

    configure_initial_value(ValueWidth'(MaxValue));
    td.reset_dut();
    reset_scoreboard();
    wait_idle_cycles(2);
  endtask

  task automatic test_idle_noop();
    // Intent: Verify idle cycles leave value stable and available follows value/withhold.
    $display("Running test_idle_noop");
    init_interfaces();
    configure_initial_value(ValueWidth'(MaxValue / 2));
    td.reset_dut();
    reset_scoreboard();
    wait_idle_cycles(4);
  endtask

  task automatic test_increment_only();
    // Intent: Exercise increment-only updates, including maximum and optional zero increments.
    int increment;  // Legal increment amount chosen for the current cycle.

    $display("Running test_increment_only");
    init_interfaces();
    configure_initial_value('0);
    td.reset_dut();
    reset_scoreboard();

    if (EnableCoverZeroIncrement) begin
      drive_cycle(1'b1, '0, 1'b0, '0, '0);
    end

    while (expected_value < ValueWidth'(MaxValue)) begin
      increment = int'(MaxValue) - int'(expected_value);
      if (increment > int'(MaxIncrement)) begin
        increment = int'(MaxIncrement);
      end
      drive_cycle(1'b1, ChangeWidth'(increment), 1'b0, '0, '0);
    end
  endtask

  task automatic test_decrement_only();
    // Intent: Exercise decrement-only updates, including maximum and optional zero decrements.
    int decrement;  // Legal decrement amount chosen for the current cycle.

    $display("Running test_decrement_only");
    init_interfaces();
    configure_initial_value(ValueWidth'(MaxValue));
    td.reset_dut();
    reset_scoreboard();

    if (EnableCoverZeroDecrement) begin
      drive_cycle(1'b0, '0, 1'b1, '0, '0);
    end

    while (expected_value > '0) begin
      decrement = int'(expected_value);
      if (decrement > int'(MaxDecrement)) begin
        decrement = int'(MaxDecrement);
      end
      drive_cycle(1'b0, '0, 1'b1, ChangeWidth'(decrement), '0);
    end
  endtask

  task automatic test_simultaneous_increment_decrement();
    // Intent: Exercise concurrent increment/decrement updates with equal and unequal amounts.
    $display("Running test_simultaneous_increment_decrement");
    init_interfaces();
    configure_initial_value(ValueWidth'(MaxValue / 2));
    td.reset_dut();
    reset_scoreboard();

    if (MaxValue >= 1) begin
      drive_cycle(1'b1, ChangeWidth'(1), 1'b1, ChangeWidth'(1), '0);
    end

    if ((MaxIncrement > 1) && (expected_value < ValueWidth'(MaxValue))) begin
      drive_cycle(1'b1, ChangeWidth'(2), 1'b1, ChangeWidth'(1), '0);
    end

    if ((MaxDecrement > 1) && (expected_value >= ValueWidth'(2))) begin
      drive_cycle(1'b1, ChangeWidth'(1), 1'b1, ChangeWidth'(2), '0);
    end
  endtask

  task automatic test_withhold_available();
    // Intent: Verify withhold reduces available credit and clips available at zero.
    $display("Running test_withhold_available");
    init_interfaces();
    configure_initial_value(ValueWidth'(MaxValue));
    td.reset_dut();
    reset_scoreboard();

    if (EnableCoverWithhold) begin
      drive_cycle(1'b0, '0, 1'b0, '0, ValueWidth'(1));
      drive_cycle(1'b0, '0, 1'b0, '0, ValueWidth'(MaxValue));

      configure_initial_value('0);
      td.reset_dut();
      reset_scoreboard();
      drive_cycle(1'b0, '0, 1'b0, '0, ValueWidth'(MaxValue));
    end else begin
      wait_idle_cycles(2);
    end
  endtask

  task automatic test_decrement_backpressure();
    // Intent: Exercise decr_valid requests that exceed available credit when backpressure is legal.
    $display("Running test_decrement_backpressure");
    init_interfaces();
    configure_initial_value('0);
    td.reset_dut();
    reset_scoreboard();

    if (EnableCoverDecrementBackpressure) begin
      drive_cycle(1'b0, '0, 1'b1, ChangeWidth'(1), '0);
    end else begin
      wait_idle_cycles(2);
    end
  endtask

  task automatic test_no_decrement_backpressure_mode();
    // Intent: Keep decrement requests within available credit when no-backpressure mode is enabled.
    $display("Running test_no_decrement_backpressure_mode");
    init_interfaces();
    configure_initial_value(ValueWidth'(MaxValue));
    td.reset_dut();
    reset_scoreboard();

    while (expected_value > '0) begin
      drive_cycle(1'b0, '0, 1'b1, ChangeWidth'(1), '0);
    end
  endtask

  task automatic test_random();
    // Intent: Run bounded pseudo-random legal increment, decrement, and withhold traffic.
    logic next_incr_valid;  // Random increment valid for the next cycle.
    logic [ChangeWidth-1:0] next_incr;  // Random increment amount for the next cycle.
    logic next_decr_valid;  // Random decrement valid for the next cycle.
    logic [ChangeWidth-1:0] next_decr;  // Random decrement amount for the next cycle.
    logic [ValueWidth-1:0] next_withhold;  // Random withhold amount for the next cycle.
    logic [ValueWidth-1:0] random_available;  // Predicted available credit for decr sizing.
    int max_increment;  // Maximum legal random increment for the next cycle.
    int max_decrement;  // Maximum legal random decrement for the next cycle.

    $display("Running test_random");
    init_interfaces();
    configure_initial_value(ValueWidth'(MaxValue / 2));
    td.reset_dut();
    reset_scoreboard();

    for (int i = 0; i < NumRandomCycles; i++) begin
      max_increment = int'(MaxValue) - int'(expected_value);
      if (max_increment > int'(MaxIncrement)) begin
        max_increment = int'(MaxIncrement);
      end

      next_incr_valid = (max_increment > 0) && ($urandom_range(0, 99) < 55);
      next_incr = next_incr_valid ? ChangeWidth'($urandom_range(1, max_increment)) : '0;

      if (EnableCoverZeroIncrement && ($urandom_range(0, 99) < 10)) begin
        next_incr_valid = 1'b1;
        next_incr = '0;
      end

      if (EnableCoverWithhold) begin
        next_withhold = ValueWidth'($urandom_range(0, int'(MaxValue)));
      end else begin
        next_withhold = '0;
      end

      random_available = get_available(expected_value, next_incr_valid, next_incr, next_withhold);
      max_decrement = int'(MaxDecrement);
      if (!EnableCoverDecrementBackpressure || EnableAssertNoDecrementBackpressure) begin
        if (max_decrement > int'(random_available)) begin
          max_decrement = int'(random_available);
        end
      end

      next_decr_valid = (max_decrement > 0) && ($urandom_range(0, 99) < 55);
      next_decr = next_decr_valid ? ChangeWidth'($urandom_range(1, max_decrement)) : '0;

      if (EnableCoverZeroDecrement && ($urandom_range(0, 99) < 10)) begin
        next_decr_valid = 1'b1;
        next_decr = '0;
      end

      drive_cycle(next_incr_valid, next_incr, next_decr_valid, next_decr, next_withhold);
    end
  endtask

  task automatic run_all_tests();
    // Intent: Sequence all directed scenarios, random traffic, final checks, and finish reporting.
    test_reset_initial_value();
    test_idle_noop();
    test_increment_only();
    // test_decrement_only();
    test_simultaneous_increment_decrement();
    test_withhold_available();
    test_decrement_backpressure();
    test_no_decrement_backpressure_mode();
    test_random();

    td.check(saw_max_increment, "max increment was not observed");
    td.check(saw_max_decrement, "max decrement was not observed");
    td.check(saw_simultaneous_incr_decr, "simultaneous increment/decrement was not observed");
    td.check(saw_value_zero, "value zero was not observed");
    td.check(saw_value_max, "CoverMaxValue was not observed");
    if (EnableCoverZeroIncrement) begin
      td.check(saw_zero_increment, "zero increment was not observed");
    end
    if (EnableCoverZeroDecrement) begin
      td.check(saw_zero_decrement, "zero decrement was not observed");
    end
    if (EnableCoverDecrementBackpressure) begin
      td.check(saw_decrement_backpressure, "decrement backpressure was not observed");
    end
    if (EnableCoverWithhold) begin
      td.check(saw_withhold, "withhold was not observed");
    end
  endtask

  initial begin
    init_interfaces();
    reset_scoreboard();

    fork
      monitor_enable();
    join_none

    run_all_tests();
    init_interfaces();
    td.finish(5);
  end

endmodule : br_credit_counter_tb
