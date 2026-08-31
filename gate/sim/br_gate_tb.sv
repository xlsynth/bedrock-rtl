// Testbench for various br_gate behavioral modules.
// Modules involving CDC or clock buffer/invert are not included.
// TODO(zhemao): Determine how to get test coverage for CDC and clock converter.

module br_gate_tb;
  logic in0;
  logic in1;
  logic in2;
  logic in3;
  logic [1:0] sel;

  logic out_buf;
  logic out_inv;
  logic out_and;
  logic out_or;
  logic out_xor;
  logic out_mux2;
  logic out_mux4;

  br_gate_buf br_gate_buf_inst (
      .in (in0),
      .out(out_buf)
  );

  br_gate_inv br_gate_inv_inst (
      .in (in0),
      .out(out_inv)
  );

  br_gate_and2 br_gate_and2_inst (
      .in0(in0),
      .in1(in1),
      .out(out_and)
  );

  br_gate_or2 br_gate_or2_inst (
      .in0(in0),
      .in1(in1),
      .out(out_or)
  );

  br_gate_xor2 br_gate_xor2_inst (
      .in0(in0),
      .in1(in1),
      .out(out_xor)
  );

  br_gate_mux2 br_gate_mux2_inst (
      .in0(in0),
      .in1(in1),
      .sel(sel[0]),
      .out(out_mux2)
  );

  br_gate_mux4 br_gate_mux4_inst (
      .in0(in0),
      .in1(in1),
      .in2(in2),
      .in3(in3),
      .sel(sel),
      .out(out_mux4)
  );

  // Every combination of inputs
  localparam int NumTests = 64;

  logic expected_out_buf;
  logic expected_out_inv;
  logic expected_out_and;
  logic expected_out_or;
  logic expected_out_xor;
  logic expected_out_mux2;
  logic expected_out_mux4;

  logic clk;
  logic rst;

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    in0 = 1'b0;
    in1 = 1'b0;
    in2 = 1'b0;
    in3 = 1'b0;
    sel = 2'b00;
    td.reset_dut();
    td.wait_cycles();

    for (int i = 0; i < NumTests; i++) begin
      {in0, in1, in2, in3, sel} = i[5:0];
      expected_out_buf = in0;
      expected_out_inv = ~in0;
      expected_out_and = in0 && in1;
      expected_out_or = in0 || in1;
      expected_out_xor = in0 ^ in1;
      expected_out_mux2 = sel[0] ? in1 : in0;
      expected_out_mux4 = (sel == 2'b00) ? in0 :
                          (sel == 2'b01) ? in1 :
                          (sel == 2'b10) ? in2 :
                          (sel == 2'b11) ? in3 : 1'b0;
      @(posedge clk);
      td.check_integer(out_buf, expected_out_buf, $sformatf(
                       "Test failed for out_buf at index %0d", i));
      td.check_integer(out_inv, expected_out_inv, $sformatf(
                       "Test failed for out_inv at index %0d", i));
      td.check_integer(out_and, expected_out_and, $sformatf(
                       "Test failed for out_and at index %0d", i));
      td.check_integer(out_or, expected_out_or, $sformatf("Test failed for out_or at index %0d", i
                       ));
      td.check_integer(out_xor, expected_out_xor, $sformatf(
                       "Test failed for out_xor at index %0d", i));
      td.check_integer(out_mux2, expected_out_mux2, $sformatf(
                       "Test failed for out_mux2 at index %0d", i));
      td.check_integer(out_mux4, expected_out_mux4, $sformatf(
                       "Test failed for out_mux4 at index %0d", i));
      @(negedge clk);
    end

    td.finish();
  end

endmodule
