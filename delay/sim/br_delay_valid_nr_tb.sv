// SPDX-License-Identifier: Apache-2.0

module br_delay_valid_nr_tb;

  parameter int Width = 8;
  parameter int NumStages = 2;
  parameter bit FirstStageUngated = 0;
  parameter int NumTestCycles = 16;

  logic clk;
  logic rst;
  logic in_valid;
  logic [Width-1:0] in;
  logic out_valid;
  logic [Width-1:0] out;
  logic [NumStages:0] out_valid_stages;
  logic [NumStages:0][Width-1:0] out_stages;

  logic [NumStages:0] model_valid;
  logic [NumStages:0][Width-1:0] model_data;
  logic [NumStages:0] next_valid;
  logic [NumStages:0][Width-1:0] next_data;

  br_delay_valid_nr #(
      .Width(Width),
      .NumStages(NumStages),
      .FirstStageUngated(FirstStageUngated)
  ) dut (
      .clk,
      .in_valid,
      .in,
      .out_valid,
      .out,
      .out_valid_stages,
      .out_stages
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [Width-1:0] data_for(input int idx);
    for (int i = 0; i < Width; i++) begin
      data_for[i] = ((idx + (3 * i)) % 5) < 2;
    end
  endfunction

  function automatic logic valid_for(input int idx);
    valid_for = (idx % 5) != 1;
  endfunction

  task automatic update_model(input logic drive_valid, input logic [Width-1:0] drive_data);
    next_valid[0] = drive_valid;
    next_data[0]  = drive_data;

    for (int i = 1; i <= NumStages; i++) begin
      logic prev_valid;
      logic [Width-1:0] prev_data;

      prev_valid = (i == 1) ? drive_valid : model_valid[i-1];
      prev_data  = (i == 1) ? drive_data : model_data[i-1];

      next_valid[i] = prev_valid;
      next_data[i]  = model_data[i];
      if (prev_valid || (FirstStageUngated && i == 1)) begin
        next_data[i] = prev_data;
      end
    end

    model_valid = next_valid;
    model_data  = next_data;
  endtask

  task automatic check_model(input string phase);
    td.check(out_valid === model_valid[NumStages],
             $sformatf("%s: out_valid mismatch", phase));
    td.check(out_valid_stages === model_valid,
             $sformatf("%s: out_valid_stages mismatch", phase));

    for (int i = 0; i <= NumStages; i++) begin
      if (model_valid[i]) begin
        td.check(out_stages[i] === model_data[i],
                 $sformatf("%s: out_stages[%0d] mismatch", phase, i));
      end
    end

    if (model_valid[NumStages]) begin
      td.check(out === model_data[NumStages], $sformatf("%s: out mismatch", phase));
    end
  endtask

  task automatic drive_cycle(input logic drive_valid, input logic [Width-1:0] drive_data,
                             input string phase);
    in_valid = drive_valid;
    in = drive_data;
    td.wait_cycles();
    update_model(drive_valid, drive_data);
    check_model(phase);
  endtask

  initial begin
    in_valid = 1'b0;
    in = '0;
    model_valid = '0;
    model_data = '0;
    next_valid = '0;
    next_data = '0;

    td.reset_dut();

    for (int i = 0; i < NumStages + 2; i++) begin
      in_valid = 1'b0;
      in = data_for(-i - 1);
      td.wait_cycles();
    end

    for (int i = 0; i < NumTestCycles; i++) begin
      drive_cycle(valid_for(i), valid_for(i) ? data_for(i) : data_for(-i - 1),
                  $sformatf("directed cycle %0d", i));
    end

    for (int i = 0; i < NumStages + 2; i++) begin
      drive_cycle(1'b0, data_for(NumTestCycles + i), $sformatf("drain cycle %0d", i));
    end

    td.finish();
  end

endmodule : br_delay_valid_nr_tb
