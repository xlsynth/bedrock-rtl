// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

module br_fifo_shared_pstatic_flops_tb;
  parameter int MaxRandomDelay = 4;
  parameter int TestSize = 1000;
  parameter int NumFifos = 2;
  parameter int Depth = 5;
  parameter int Width = 8;
  parameter int StagingBufferDepth = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter int RamAddressDepthStages = 0;

  localparam int FifoIdWidth = $clog2(NumFifos);
  localparam int AddrWidth = $clog2(Depth);

  logic clk;
  logic rst;
  logic start;
  logic finished;
  logic [31:0] error_count;

  logic [NumFifos-1:0][AddrWidth-1:0] config_base;
  logic [NumFifos-1:0][AddrWidth-1:0] config_bound;
  logic config_error;

  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;
  logic [FifoIdWidth-1:0] push_fifo_id;

  logic [NumFifos-1:0] pop_ready;
  logic [NumFifos-1:0] pop_valid;
  logic [NumFifos-1:0][Width-1:0] pop_data;

  br_fifo_shared_pstatic_flops #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamAddressDepthStages(RamAddressDepthStages)
  ) dut (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
      .push_ready,
      .push_valid,
      .push_data,
      .push_fifo_id,
      .push_full(),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty()
  );

  br_test_driver td (
      .clk,
      .rst
  );

  br_fifo_shared_test_harness #(
      .NumFifos(NumFifos),
      .NumWritePorts(1),
      .Width(Width),
      .TestSize(TestSize),
      .MaxRandomDelay(MaxRandomDelay)
  ) br_fifo_shared_test_harness (
      .clk,
      .rst,
      .start,
      .finished,
      .error_count,
      .push_ready,
      .push_valid,
      .push_data,
      .push_fifo_id,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  initial begin
    start = 0;
    config_base[0] = 0;
    config_bound[0] = (Depth / NumFifos) - 1;
    for (int i = 1; i < NumFifos; i++) begin
      config_base[i]  = config_bound[i-1] + 1;
      config_bound[i] = config_base[i] + (Depth / NumFifos) - 1;
    end

    td.reset_dut();

    td.check(!config_error, "FIFO configuration error");

    start = 1;
    td.wait_cycles(1);

    while (!finished) begin
      td.wait_cycles();
    end

    if (error_count != 0) begin
      $display("ERROR: %d errors occurred", error_count);
    end else begin
      td.finish();
    end
  end

endmodule
