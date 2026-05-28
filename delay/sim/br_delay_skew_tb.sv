// SPDX-License-Identifier: Apache-2.0

module br_delay_skew_tb;

  parameter int Width = 8;

  logic clk;
  logic rst;
  logic in_valid;
  logic [Width-1:0] in;
  logic out_valid_next;
  logic [Width-1:0] out;
  logic [Width-1:0] expected_out;
  logic expected_out_known;

  br_delay_skew #(
      .Width(Width)
  ) dut (
      .clk,
      .in_valid,
      .in,
      .out_valid_next,
      .out
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [Width-1:0] data_for(input int idx);
    for (int i = 0; i < Width; i++) begin
      data_for[i] = ((idx + (2 * i)) % 3) != 0;
    end
  endfunction

  task automatic drive_cycle(input logic drive_valid, input logic [Width-1:0] drive_data,
                             input string phase);
    in_valid = drive_valid;
    in = drive_data;
    td.wait_cycles();
    td.check(out_valid_next === drive_valid, $sformatf("%s: out_valid_next mismatch", phase));

    if (drive_valid) begin
      expected_out = drive_data;
      expected_out_known = 1'b1;
    end

    if (expected_out_known) begin
      td.check(out === expected_out, $sformatf("%s: out mismatch", phase));
    end
  endtask

  initial begin
    in_valid = 1'b0;
    in = '0;
    expected_out = '0;
    expected_out_known = 1'b0;

    td.reset_dut();

    drive_cycle(1'b1, data_for(0), "first valid beat");
    drive_cycle(1'b1, data_for(1), "back-to-back beat");
    drive_cycle(1'b0, data_for(2), "invalid hold");
    drive_cycle(1'b1, data_for(3), "valid after bubble");
    drive_cycle(1'b0, data_for(4), "drain");
    drive_cycle(1'b0, data_for(5), "final idle");

    td.finish();
  end

endmodule : br_delay_skew_tb
