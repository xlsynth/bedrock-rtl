// SPDX-License-Identifier: Apache-2.0

// Directed simulation testbench for br_cdc_bit_toggle.
//
// Scope:
// - initial convergence from unknown synchronizer state to a stable source value
// - directed low-to-high and high-to-low source level changes
// - destination data checks for every source transition
// - a directed short pulse that must be observed at the destination
// - fast-source to slow-destination crossings with minimum observable source spacing
// - asynchronous source/destination clock ratios
// - Bazel-swept NumStages, AddSourceFlop, SrcClkPeriod, and DstClkPeriod parameters

module br_cdc_bit_toggle_tb;
  timeunit 1ns; timeprecision 1ps;

  parameter int NumStages = 3;
  parameter bit AddSourceFlop = 1;
  parameter int SrcClkPeriod = 10;
  parameter int DstClkPeriod = 14;
  parameter int MaxResetCycles = 10;
  parameter int NumTransitions = 12;

  localparam logic LowBitValue = 1'b0;
  localparam logic HighBitValue = 1'b1;
  localparam realtime SrcClkHalfPeriod = SrcClkPeriod / 2.0;
  localparam realtime DstClkHalfPeriod = DstClkPeriod / 2.0;
  localparam int SourceUpdateCycles = AddSourceFlop ? 2 : 1;
  localparam int MinResetTime = SourceUpdateCycles * SrcClkPeriod + (NumStages + 2) * DstClkPeriod;
  // The destination can only observe a source update after the optional source
  // flop, a possible simulation delay, and NumStages destination samples.
  // Convert the source-domain setup time to destination cycles and add margin
  // for arbitrary clock phase.
  localparam int DstTimeoutCycles = br_math::ceil_div(
      (SourceUpdateCycles + 2) * SrcClkPeriod, DstClkPeriod
  ) + NumStages + 4;
  // Hold directed pulses long enough to span two destination periods,
  // expressed in source cycles, plus the source-side update latency.
  localparam int MinObservableSrcCycles = SourceUpdateCycles + br_math::ceil_div(
      2 * DstClkPeriod, SrcClkPeriod
  ) + 1;
  localparam int NumFastToSlowTransitions = 4;

  logic src_clk;
  logic src_rst;
  logic src_bit;

  logic dst_clk;
  logic dst_rst;
  logic dst_bit;

  logic td_clk;
  logic td_rst;

  br_cdc_bit_toggle #(
      .NumStages(NumStages),
      .AddSourceFlop(AddSourceFlop)
  ) dut (
      .src_clk,
      .src_rst,
      .src_bit,
      .dst_clk,
      .dst_rst,
      .dst_bit
  );

  always #SrcClkHalfPeriod src_clk = ~src_clk;
  always #DstClkHalfPeriod dst_clk = ~dst_clk;

  br_test_driver td (
      .clk(td_clk),
      .rst(td_rst)
  );

  task automatic record_failure(input string message);
    td.check(1'b0, message);
  endtask

  task automatic wait_for_dst_bit(input logic expected);
    int timeout;

    timeout = DstTimeoutCycles;
    while (timeout > 0 && dst_bit !== expected) begin
      @(posedge dst_clk);
      timeout--;
    end

    if (dst_bit !== expected) begin
      record_failure($sformatf(
                     "timed out waiting for dst_bit=%0b, got %0b after %0d destination cycles",
                     expected,
                     dst_bit,
                     DstTimeoutCycles
                     ));
    end
  endtask

  task automatic check_dst_stable(input logic expected);
    repeat (2) begin
      @(posedge dst_clk);
      if (dst_bit !== expected) begin
        record_failure($sformatf(
                       "dst_bit changed unexpectedly, expected %0b got %0b", expected, dst_bit));
      end
    end
  endtask

  task automatic drive_and_check(input logic value);
    @(negedge src_clk);
    src_bit <= value;
    wait_for_dst_bit(value);
    check_dst_stable(value);
  endtask

  // Drive a source value and keep it stable for a caller-selected number of
  // source cycles before checking destination convergence.
  task automatic drive_and_check_after_hold(input logic value, input int src_hold_cycles);
    @(negedge src_clk);
    src_bit <= value;
    repeat (src_hold_cycles) @(posedge src_clk);
    wait_for_dst_bit(value);
    check_dst_stable(value);
  endtask

  // Exercise a pulse-like level change: high long enough to be observable at
  // the destination, then return low and verify both phases.
  task automatic drive_short_pulse();
    drive_and_check_after_hold(HighBitValue, MinObservableSrcCycles);
    drive_and_check(LowBitValue);
  endtask

  // When the source clock is faster than the destination clock, drive changes
  // with the minimum spacing that should still be observable.
  task automatic drive_fast_to_slow_burst();
    logic value;

    if (SrcClkPeriod >= DstClkPeriod) begin
      return;
    end

    value = src_bit;
    for (int i = 0; i < NumFastToSlowTransitions; i++) begin
      value = !value;
      drive_and_check_after_hold(value, MinObservableSrcCycles);
    end
  endtask

  initial begin
    static br_cdc_pkg::cdc_delay_mode_t cdc_delay_mode = br_cdc_pkg::CdcDelayNone;
    int src_reset_cycles;
    int dst_reset_cycles;
    logic expected;

    void'($value$plusargs("cdc_delay_mode=%d", cdc_delay_mode));
    $display("set cdc_delay_mode = %0s", cdc_delay_mode.name());
`ifdef SIMULATION
    br_cdc_pkg::cdc_delay_mode = cdc_delay_mode;
`endif

    src_clk = 1'b0;
    dst_clk = 1'b0;
    src_rst = 1'b1;
    dst_rst = 1'b1;
    src_bit = LowBitValue;

    #MinResetTime;

    src_reset_cycles = $urandom_range(0, MaxResetCycles);
    dst_reset_cycles = $urandom_range(0, MaxResetCycles);

    fork
      begin
        repeat (src_reset_cycles) @(posedge src_clk);
        src_rst <= 1'b0;
      end
      begin
        repeat (dst_reset_cycles) @(posedge dst_clk);
        dst_rst <= 1'b0;
      end
    join

    $display("Checking initial zero convergence");
    wait_for_dst_bit(LowBitValue);
    check_dst_stable(LowBitValue);

    $display("Checking directed short pulse");
    drive_short_pulse();

    $display("Checking fast-source to slow-destination transitions");
    drive_fast_to_slow_burst();

    // Toggle the source level after randomized spacing and check that every
    // new value propagates to the destination domain and remains stable.
    expected = src_bit;

    $display("Checking directed source transitions");
    for (int i = 0; i < NumTransitions; i++) begin
      int src_spacing;

      expected = !expected;
      src_spacing = $urandom_range(SourceUpdateCycles + 1, SourceUpdateCycles + 4);
      repeat (src_spacing) @(posedge src_clk);
      drive_and_check(expected);
    end

    td.finish();
  end

endmodule : br_cdc_bit_toggle_tb
