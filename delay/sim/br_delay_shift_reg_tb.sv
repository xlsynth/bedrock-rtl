// SPDX-License-Identifier: Apache-2.0

module br_delay_shift_reg_tb;

  parameter int Width = 8;
  parameter int NumStages = 3;
  parameter bit EnableCoverReinit = 1;
  parameter int NumTestCycles = 24;

  logic clk;
  logic rst;
  logic reinit;
  logic [NumStages-1:0][Width-1:0] initial_value;
  logic [NumStages-1:0][Width-1:0] value;
  logic shift_en;
  logic [Width-1:0] shift_in;
  logic [Width-1:0] shift_out;

  logic [NumStages-1:0][Width-1:0] model_value;
  logic [NumStages-1:0][Width-1:0] next_value;
  logic [NumStages-1:0][Width-1:0] temp_value;

  br_delay_shift_reg #(
      .Width(Width),
      .NumStages(NumStages),
      .EnableCoverReinit(EnableCoverReinit)
  ) dut (
      .clk,
      .rst,
      .reinit,
      .initial_value,
      .value,
      .shift_en,
      .shift_in,
      .shift_out
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [Width-1:0] data_for(input int idx);
    for (int i = 0; i < Width; i++) begin
      data_for[i] = ((idx + (5 * i)) % 11) < 6;
    end
  endfunction

  function automatic logic [NumStages-1:0][Width-1:0] initial_value_for(input int idx);
    for (int i = 0; i < NumStages; i++) begin
      initial_value_for[i] = data_for(idx + (3 * i));
    end
  endfunction

  task automatic check_model(input string phase);
    for (int i = 0; i < NumStages; i++) begin
      td.check(value[i] === model_value[i], $sformatf("%s: value[%0d] mismatch", phase, i));
    end
    td.check(shift_out === model_value[NumStages-1], $sformatf("%s: shift_out mismatch", phase));
  endtask

  task automatic update_model(input logic drive_reinit, input logic drive_shift_en,
                              input logic [NumStages-1:0][Width-1:0] drive_initial_value,
                              input logic [Width-1:0] drive_shift_in);
    temp_value = drive_reinit ? drive_initial_value : model_value;

    if (drive_shift_en) begin
      next_value[0] = drive_shift_in;
      for (int i = 1; i < NumStages; i++) begin
        next_value[i] = temp_value[i-1];
      end
    end else begin
      next_value = temp_value;
    end

    model_value = next_value;
  endtask

  task automatic drive_cycle(input logic drive_reinit, input logic drive_shift_en,
                             input logic [NumStages-1:0][Width-1:0] drive_initial_value,
                             input logic [Width-1:0] drive_shift_in, input string phase);
    reinit = drive_reinit;
    shift_en = drive_shift_en;
    initial_value = drive_initial_value;
    shift_in = drive_shift_in;

    td.wait_cycles();
    update_model(drive_reinit, drive_shift_en, drive_initial_value, drive_shift_in);
    check_model(phase);
  endtask

  initial begin
    reinit = 1'b0;
    shift_en = 1'b0;
    initial_value = initial_value_for(0);
    shift_in = data_for(0);
    model_value = '0;
    next_value = '0;
    temp_value = '0;

    td.reset_dut();

    model_value = initial_value;
    check_model("after reset");

    for (int i = 0; i < 3; i++) begin
      drive_cycle(1'b0, 1'b0, initial_value_for(10 + i), data_for(20 + i), $sformatf(
                  "hold cycle %0d", i));
    end

    for (int i = 0; i < NumStages + 2; i++) begin
      drive_cycle(1'b0, 1'b1, initial_value_for(30 + i), data_for(40 + i), $sformatf(
                  "shift cycle %0d", i));
    end

    drive_cycle(1'b0, 1'b0, initial_value_for(50), data_for(60), "hold after shift");

    if (EnableCoverReinit) begin
      drive_cycle(1'b1, 1'b0, initial_value_for(70), data_for(80), "reinit without shift");
      drive_cycle(1'b1, 1'b1, initial_value_for(90), data_for(100), "reinit with shift");
    end

    for (int i = 0; i < NumTestCycles; i++) begin
      logic drive_reinit;
      logic drive_shift_en;

      drive_reinit   = EnableCoverReinit && (i % 7 == 3);
      drive_shift_en = (i % 4) != 1;

      drive_cycle(drive_reinit, drive_shift_en, initial_value_for(110 + i), data_for(140 + i),
                  $sformatf("directed cycle %0d", i));
    end

    for (int i = 0; i < NumStages + 2; i++) begin
      drive_cycle(1'b0, 1'b1, initial_value_for(170 + i), data_for(200 + i), $sformatf(
                  "drain cycle %0d", i));
    end

    td.finish();
  end

endmodule : br_delay_shift_reg_tb
