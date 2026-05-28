// SPDX-License-Identifier: Apache-2.0

module br_delay_deskew_tb;

  parameter int Width = 8;

  logic clk;
  logic rst;
  logic in_valid_next;
  logic [Width-1:0] in;
  logic out_valid;
  logic [Width-1:0] out;

  br_delay_deskew #(
      .Width(Width)
  ) dut (
      .clk,
      .in_valid_next,
      .in,
      .out_valid,
      .out
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [Width-1:0] data_for(input int idx);
    for (int i = 0; i < Width; i++) begin
      data_for[i] = ((idx + i) % 4) < 2;
    end
  endfunction

  task automatic drive_cycle(input logic drive_valid_next, input logic expected_valid,
                             input logic [Width-1:0] drive_data, input string phase);
    in_valid_next = drive_valid_next;
    td.wait_cycles();
    in = drive_data;
    #1;
    td.check(out_valid === expected_valid, $sformatf("%s: out_valid mismatch", phase));
    if (expected_valid) begin
      td.check(out === drive_data, $sformatf("%s: out mismatch", phase));
    end
  endtask

  initial begin
    in_valid_next = 1'b0;
    in = '0;

    td.reset_dut();

    drive_cycle(1'b0, 1'b0, data_for(-1), "initial idle");
    drive_cycle(1'b1, 1'b1, data_for(0), "first valid beat");
    drive_cycle(1'b1, 1'b1, data_for(1), "back-to-back beat");
    drive_cycle(1'b0, 1'b0, data_for(2), "bubble");
    drive_cycle(1'b1, 1'b1, data_for(3), "valid after bubble");
    drive_cycle(1'b0, 1'b0, data_for(4), "final idle");

    td.finish();
  end

endmodule : br_delay_deskew_tb
