// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

module br_fifo_flops_tb;

  // Parameters
  parameter int Depth = 13;
  parameter int Width = 8;
  parameter int EnableBypass = 1;
  parameter int RegisterPopOutputs = 0;
  parameter int FlopRamAddressDepthStages = 0;

  localparam int CutThroughLatency =
      (EnableBypass ? 0 : (FlopRamAddressDepthStages + 1)) + RegisterPopOutputs;
  localparam int BackpressureLatency = 1;

  // Clock and Reset
  reg clk;
  reg rst;

  logic start;
  logic finished;
  logic [31:0] error_count;

  // Push Interface
  wire push_ready;
  reg push_valid;
  reg [Width-1:0] push_data;

  // Pop Interface
  reg pop_ready;
  wire pop_valid;
  wire [Width-1:0] pop_data;

  // Status Outputs
  wire empty;
  wire full;
  wire [$clog2(Depth+1)-1:0] items;
  wire [$clog2(Depth+1)-1:0] slots;

  // Instantiate the FIFO
  br_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .EnableBypass(EnableBypass),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages)
  ) dut (
      .clk(clk),
      .rst(rst),
      .push_ready(push_ready),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(pop_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .empty(empty),
      .empty_next(),
      .slots(),
      .slots_next(),
      .full(full),
      .full_next(),
      .items(items),
      .items_next()
  );

  // Hook up the test harness
  br_fifo_test_harness #(
      .Depth(Depth),
      .Width(Width),
      .CutThroughLatency(CutThroughLatency),
      .BackpressureLatency(BackpressureLatency)
  ) br_fifo_test_harness (
      .clk,
      .rst,
      .start      (start),
      .finished   (finished),
      .error_count(error_count),
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty,
      .full,
      .items,
      .slots
  );

`ifdef DUMP_WAVES
  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
`endif

  br_test_driver td (
      .clk,
      .rst
  );

  // Test Sequence
  initial begin
    integer timeout;

    start = 0;

    td.reset_dut();

    $display("Starting test");

    start   = 1'b1;

    timeout = 5000;
    td.wait_cycles();
    while (timeout > 0 && !finished) begin
      td.wait_cycles();
      timeout = timeout - 1;
    end

    td.check(timeout > 0, $sformatf("Test timed out"));
    td.check(error_count == 0, $sformatf("Errors in test"));

    td.finish();
  end

endmodule
