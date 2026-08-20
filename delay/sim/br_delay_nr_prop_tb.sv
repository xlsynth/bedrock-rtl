// SPDX-License-Identifier: Apache-2.0

// Requires four-state simulation to check unknown startup and reset masking.
module br_delay_nr_prop_tb;

  parameter int Width = 8;
  parameter int NumStages = 2;

  localparam int NumTestCycles = 16;

  logic clk;
  logic rst;
  logic [Width-1:0] in;
  logic [Width-1:0] out;
  logic [NumStages:0][Width-1:0] out_stages;
  logic [NumStages:0][Width-1:0] model_data;

  br_delay_nr_prop #(
      .Width(Width),
      .NumStages(NumStages)
  ) dut (
      .clk,
      .rst,
      .in,
      .out,
      .out_stages
  );

  br_test_driver #(
      .ResetCycles(NumStages + 1)
  ) td (
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
    td.check(out_stages === model_data, $sformatf("%s: out_stages mismatch", phase));
  endtask

  task automatic drive_cycle(input logic [Width-1:0] drive_data, input string phase);
    logic [NumStages:0][Width-1:0] next_data;
    in = drive_data;
    td.wait_cycles();
    next_data[0] = drive_data;
    for (int i = 1; i <= NumStages; i++) begin
      next_data[i] = (i == 1) ? drive_data : model_data[i-1];
    end
    model_data = next_data;
    check_model(phase);
  endtask

  task automatic fill(input logic [Width-1:0] drive_data, input string phase);
    for (int i = 0; i <= NumStages; i++) begin
      drive_cycle(drive_data, phase);
    end
  endtask

  initial begin
    in = 'x;
    model_data = 'x;

    // The driver starts with rst asserted. Unknown data must propagate unchanged
    // without tripping the known-value assertion while the consumer is in reset.
    fill('x, "startup X");
    td.check($isunknown(out), "Startup X must reach the output");
    fill('z, "startup Z");
    td.check($isunknown(out), "Startup Z must reach the output");

    // Flush known data before releasing the consumer reset.
    fill(data_for(0), "startup flush");
    td.reset_dut();
    check_model("reset release");
    for (int i = 0; i < NumTestCycles; i++) begin
      drive_cycle(data_for(i + 1), $sformatf("known cycle %0d", i));
    end

    // Reasserting consumer reset must not reset any pipeline register.
    fill('1, "before consumer reset");
    td.reset_dut();
    check_model("consumer reset preserves data");
    for (int i = 0; i < NumStages + 2; i++) begin
      drive_cycle(data_for(NumTestCycles + i + 1), "after consumer reset");
    end

    fill(data_for(0), "final flush");
    td.finish(1);
  end

endmodule : br_delay_nr_prop_tb
