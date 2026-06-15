// SPDX-License-Identifier: Apache-2.0

module br_delay_nr_tb;

  parameter int Width = 8;
  parameter int NumStages = 2;
  parameter int NumTestCycles = 18;

  logic clk;
  logic rst;
  logic [Width-1:0] in;
  logic [Width-1:0] out;
  logic [NumStages:0][Width-1:0] out_stages;

  logic [NumStages:0][Width-1:0] model_data;
  logic [NumStages:0][Width-1:0] next_data;

  br_delay_nr #(
      .Width(Width),
      .NumStages(NumStages)
  ) dut (
      .clk,
      .in,
      .out,
      .out_stages
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [Width-1:0] data_for(input int idx);
    for (int i = 0; i < Width; i++) begin
      data_for[i] = ((idx + (3 * i)) % 7) < 4;
    end
  endfunction

  task automatic check_model(input string phase);
    td.check(out === model_data[NumStages], $sformatf("%s: out mismatch", phase));
    for (int i = 0; i <= NumStages; i++) begin
      td.check(out_stages[i] === model_data[i], $sformatf("%s: out_stages[%0d] mismatch", phase, i
               ));
    end
  endtask

  task automatic update_model(input logic [Width-1:0] drive_data);
    next_data[0] = drive_data;
    for (int i = 1; i <= NumStages; i++) begin
      next_data[i] = (i == 1) ? drive_data : model_data[i-1];
    end
    model_data = next_data;
  endtask

  task automatic drive_cycle(input logic [Width-1:0] drive_data, input string phase);
    in = drive_data;
    td.wait_cycles();
    update_model(drive_data);
    check_model(phase);
  endtask

  task automatic fill_cycle(input logic [Width-1:0] drive_data);
    in = drive_data;
    td.wait_cycles();
    update_model(drive_data);
  endtask

  initial begin
    in = data_for(0);
    model_data = '0;
    next_data = '0;

    td.reset_dut();

    for (int i = 0; i < NumStages + 1; i++) begin
      fill_cycle(data_for(i));
    end
    check_model("after flush");

    for (int i = 0; i < NumTestCycles; i++) begin
      drive_cycle(data_for(i + NumStages + 1), $sformatf("directed cycle %0d", i));
    end

    for (int i = 0; i < NumStages + 2; i++) begin
      drive_cycle(data_for(NumTestCycles + NumStages + i + 1), $sformatf("drain cycle %0d", i));
    end

    td.finish();
  end

endmodule : br_delay_nr_tb
