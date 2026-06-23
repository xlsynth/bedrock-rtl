// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

/*
 * Testbench skeleton for br_mux_bin_array, an array of independent binary
 * select multiplexers sharing one input vector. The completed bench should
 * compare each output lane against a simple reference model for valid select
 * values, verify out_valid deasserts for invalid encoded select values, and
 * cover output-lane independence across directed and pseudo-random patterns.
 *
 * Planned scenarios:
 * - Idle/default input and select values after reset.
 * - Every output lane selecting every valid input.
 * - Invalid select encodings when SelectWidth has unused values.
 * - Distinct output lanes selecting distinct input symbols.
 * - Directed input data patterns such as zero, all-ones, walking bits, and lane IDs.
 * - Bounded pseudo-random select and input vectors using direct $urandom calls.
 */
module br_mux_bin_array_tb;

  // Parameters
  parameter int NumSymbolsIn = 3;
  parameter int NumSymbolsOut = 2;
  parameter int SymbolWidth = 8;
  parameter int NumRandomIterations = 64;

  localparam int SelectWidth = $clog2(NumSymbolsIn) == 0 ? 1 : $clog2(NumSymbolsIn);
  localparam int NumEncodedSelects = 1 << SelectWidth;

  // Clock and Reset
  logic clk;  // Testbench clock driven by br_test_driver.
  logic rst;  // Synchronous active-high reset driven by br_test_driver.

  // DUT interface
  logic [NumSymbolsOut-1:0][SelectWidth-1:0] select;  // Per-output binary select.
  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in;  // Shared input symbol vector.
  logic [NumSymbolsOut-1:0][SymbolWidth-1:0] out;  // Per-output selected symbol.
  logic [NumSymbolsOut-1:0] out_valid;  // Per-output select-in-range indication.

  br_mux_bin_array #(
      .NumSymbolsIn (NumSymbolsIn),
      .NumSymbolsOut(NumSymbolsOut),
      .SymbolWidth  (SymbolWidth)
  ) dut (
      .select,
      .in,
      .out,
      .out_valid
  );

`ifdef DUMP_WAVES
  initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, br_mux_bin_array_tb);
  end
`endif

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic select_is_valid(input logic [SelectWidth-1:0] select_value);
    // Intent: Return whether select_value names one of the NumSymbolsIn legal input lanes.
    select_is_valid = int'(select_value) < NumSymbolsIn;
  endfunction

  function automatic logic [SymbolWidth-1:0] expected_output(
      input logic [SelectWidth-1:0] select_value);
    // Intent: Return the reference selected input payload for a legal select value.
    if (select_is_valid(select_value)) begin
      expected_output = in[int'(select_value)];
    end else begin
      expected_output = '0;
    end
  endfunction

  task automatic init_inputs();
    // Intent: Drive all select and input symbols to deterministic idle values before reset.
    select = '0;
    in = '0;
  endtask

  task automatic set_input_lane_ids();
    // Intent: Drive each input lane with a deterministic value derived from its lane index.
    for (int i = 0; i < NumSymbolsIn; i++) begin
      in[i] = SymbolWidth'(i + 1);
    end
  endtask

  task automatic set_input_walking_bits(input int bit_offset);
    // Intent: Drive a walking-bit-style input pattern shifted by bit_offset across lanes.
    for (int i = 0; i < NumSymbolsIn; i++) begin
      in[i] = SymbolWidth'(1) << ((i + bit_offset) % SymbolWidth);
    end
  endtask

  task automatic set_input_random();
    // Intent: Drive every input lane using direct $urandom calls.
    for (int i = 0; i < NumSymbolsIn; i++) begin
      in[i] = SymbolWidth'($urandom);
    end
  endtask

  task automatic set_select_lane(input int lane_idx, input logic [SelectWidth-1:0] select_value);
    // Intent: Basic select driver for one output lane while leaving other lanes unchanged.
    td.check((lane_idx >= 0) && (lane_idx < NumSymbolsOut), "select lane index out of range");
    if ((lane_idx >= 0) && (lane_idx < NumSymbolsOut)) begin
      select[lane_idx] = select_value;
    end
  endtask

  task automatic set_select_all(input logic [SelectWidth-1:0] select_value);
    // Intent: Drive every select lane to the same encoded select value.
    for (int i = 0; i < NumSymbolsOut; i++) begin
      set_select_lane(i, select_value);
    end
  endtask

  task automatic set_select_distinct(input int offset);
    // Intent: Drive select lanes to a rotating set of valid select values to check independence.
    for (int i = 0; i < NumSymbolsOut; i++) begin
      set_select_lane(i, SelectWidth'((i + offset) % NumSymbolsIn));
    end
  endtask

  task automatic set_select_random();
    // Intent: Drive every select lane using direct $urandom calls.
    for (int i = 0; i < NumSymbolsOut; i++) begin
      set_select_lane(i, SelectWidth'($urandom_range(NumEncodedSelects - 1, 0)));
    end
  endtask

  task automatic check_output(input int output_idx);
    // Intent: Compare one output lane's out/out_valid against the reference model.
    logic expected_valid;  // Reference validity for this output lane's select value.
    logic [SymbolWidth-1:0] expected_data;  // Reference payload for this output lane.

    td.check((output_idx >= 0) && (output_idx < NumSymbolsOut), "output index out of range");
    if ((output_idx >= 0) && (output_idx < NumSymbolsOut)) begin
      expected_valid = select_is_valid(select[output_idx]);
      expected_data  = expected_output(select[output_idx]);

      td.check(out_valid[output_idx] === expected_valid, $sformatf(
               "out_valid mismatch for output %0d", output_idx));
      td.check(out[output_idx] === expected_data, $sformatf(
               "out mismatch for output %0d", output_idx));
    end
  endtask

  task automatic check_all_outputs();
    // Intent: Compare every output lane's out/out_valid against the reference model.
    for (int i = 0; i < NumSymbolsOut; i++) begin
      check_output(i);
    end
  endtask

  task automatic sample_and_check();
    // Intent: Advance one cycle with br_test_driver and then check all combinational outputs.
    td.wait_cycles();
    check_all_outputs();
  endtask

  task automatic test_idle();
    // Intent: Verify reset and all-idle select/input behavior.
    init_inputs();
    sample_and_check();
  endtask

  task automatic test_each_valid_select();
    // Intent: For every legal input select, verify each output lane selects the expected payload.
    set_input_lane_ids();
    for (int s = 0; s < NumSymbolsIn; s++) begin
      set_select_all(SelectWidth'(s));
      sample_and_check();
    end
  endtask

  task automatic test_invalid_selects();
    // Intent: Verify unused encoded select values deassert out_valid when NumSymbolsIn is not a power of two.
    set_input_lane_ids();
    for (int s = NumSymbolsIn; s < NumEncodedSelects; s++) begin
      set_select_all(SelectWidth'(s));
      sample_and_check();
    end
  endtask

  task automatic test_output_independence();
    // Intent: Drive different select values on different output lanes and verify no lane cross-coupling.
    set_input_lane_ids();
    for (int offset = 0; offset < NumSymbolsIn; offset++) begin
      set_select_distinct(offset);
      sample_and_check();
    end
  endtask

  task automatic test_input_patterns();
    // Intent: Re-run representative select checks over zero, all-ones, lane-ID, and walking-bit data.
    in = '0;
    for (int s = 0; s < NumSymbolsIn; s++) begin
      set_select_all(SelectWidth'(s));
      sample_and_check();
    end

    in = '1;
    for (int s = 0; s < NumSymbolsIn; s++) begin
      set_select_all(SelectWidth'(s));
      sample_and_check();
    end

    set_input_lane_ids();
    for (int s = 0; s < NumSymbolsIn; s++) begin
      set_select_all(SelectWidth'(s));
      sample_and_check();
    end

    for (int bit_offset = 0; bit_offset < SymbolWidth; bit_offset++) begin
      set_input_walking_bits(bit_offset);
      set_select_distinct(bit_offset);
      sample_and_check();
    end
  endtask

  task automatic test_random();
    // Intent: Run bounded pseudo-random select/input vectors using direct $urandom calls.
    for (int i = 0; i < NumRandomIterations; i++) begin
      set_input_random();
      set_select_random();
      sample_and_check();
    end
  endtask

  task automatic run_all_tests();
    // Intent: Sequence all directed scenarios, random vectors, final checks, and finish reporting.
    $display("Running test_idle");
    test_idle();
    $display("Running test_each_valid_select");
    test_each_valid_select();
    $display("Running test_invalid_selects");
    test_invalid_selects();
    $display("Running test_output_independence");
    test_output_independence();
    $display("Running test_input_patterns");
    test_input_patterns();
    $display("Running test_random");
    test_random();
  endtask

  initial begin
    init_inputs();
    td.reset_dut();
    run_all_tests();
    td.finish();
  end

endmodule : br_mux_bin_array_tb
