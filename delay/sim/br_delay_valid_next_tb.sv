// SPDX-License-Identifier: Apache-2.0

module br_delay_valid_next_tb;

  parameter int Width = 8;
  parameter int NumStages = 2;
  parameter int NumTestCycles = 18;

  logic clk;
  logic rst;
  logic in_valid_next;
  logic [Width-1:0] in;
  logic out_valid_next;
  logic [Width-1:0] out;
  logic [NumStages:0] out_valid_next_stages;
  logic [NumStages:0][Width-1:0] out_stages;

  logic [NumStages:0] model_valid_next;
  logic [NumStages:0] model_data_valid;
  logic [NumStages:0][Width-1:0] model_data;
  logic [NumStages:0] next_valid_next;
  logic [NumStages:0] next_data_valid;
  logic [NumStages:0][Width-1:0] next_data;

  br_delay_valid_next #(
      .Width(Width),
      .NumStages(NumStages)
  ) dut (
      .clk,
      .rst,
      .in_valid_next,
      .in,
      .out_valid_next,
      .out,
      .out_valid_next_stages,
      .out_stages
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [Width-1:0] data_for(input int idx);
    for (int i = 0; i < Width; i++) begin
      data_for[i] = ((idx + (5 * i)) % 7) < 3;
    end
  endfunction

  function automatic logic valid_next_for(input int idx);
    valid_next_for = (idx >= 0) && ((idx % 6) != 2) && ((idx % 6) != 5);
  endfunction

  function automatic logic [Width-1:0] drive_data_for(input int idx);
    if (valid_next_for(idx - 1)) begin
      drive_data_for = data_for(idx - 1);
    end else begin
      drive_data_for = data_for(-idx - 1);
    end
  endfunction

  task automatic update_model(input logic drive_valid_next, input logic [Width-1:0] drive_data);
    next_valid_next[0] = drive_valid_next;
    next_data_valid[0] = model_valid_next[0];
    next_data[0] = drive_data;

    for (int i = 1; i <= NumStages; i++) begin
      logic prev_valid_next;
      logic [Width-1:0] prev_data;

      prev_valid_next = (i == 1) ? drive_valid_next : model_valid_next[i-1];
      prev_data = (i == 1) ? drive_data : model_data[i-1];

      next_valid_next[i] = prev_valid_next;
      next_data_valid[i] = model_valid_next[i];
      next_data[i] = model_data[i];
      if (model_valid_next[i]) begin
        next_data[i] = prev_data;
      end
    end

    model_valid_next = next_valid_next;
    model_data_valid = next_data_valid;
    model_data = next_data;
  endtask

  task automatic check_model(input string phase);
    td.check(out_valid_next === model_valid_next[NumStages],
             $sformatf("%s: out_valid_next mismatch", phase));
    td.check(out_valid_next_stages === model_valid_next,
             $sformatf("%s: out_valid_next_stages mismatch", phase));

    for (int i = 0; i <= NumStages; i++) begin
      if (model_data_valid[i] || (NumStages == 0 && i == 0)) begin
        td.check(out_stages[i] === model_data[i],
                 $sformatf("%s: out_stages[%0d] mismatch", phase, i));
      end
    end

    if (model_data_valid[NumStages] || NumStages == 0) begin
      td.check(out === model_data[NumStages], $sformatf("%s: out mismatch", phase));
    end
  endtask

  task automatic drive_cycle(input logic drive_valid_next, input logic [Width-1:0] drive_data,
                             input string phase);
    in_valid_next = drive_valid_next;
    in = drive_data;
    td.wait_cycles();
    update_model(drive_valid_next, drive_data);
    check_model(phase);
  endtask

  initial begin
    in_valid_next = 1'b0;
    in = '0;
    model_valid_next = '0;
    model_data_valid = '0;
    model_data = '0;
    next_valid_next = '0;
    next_data_valid = '0;
    next_data = '0;

    td.reset_dut();
    check_model("after reset");

    for (int i = 0; i < NumTestCycles; i++) begin
      drive_cycle(valid_next_for(i), drive_data_for(i), $sformatf("directed cycle %0d", i));
    end

    for (int i = 0; i < NumStages + 3; i++) begin
      drive_cycle(1'b0, data_for(NumTestCycles + i), $sformatf("drain cycle %0d", i));
    end

    td.finish();
  end

endmodule : br_delay_valid_next_tb
