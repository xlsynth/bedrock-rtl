module br_fifo_shared_dynamic_flops_tb;
  parameter int MaxRandomDelay = 4;
  parameter int TestSize = 1000;
  parameter int NumFifos = 2;
  parameter int NumWritePorts = 1;
  parameter int NumReadPorts = 1;
  parameter int Depth = 5;
  parameter int Width = 8;
  parameter int StagingBufferDepth = 1;
  parameter int NumLinkedListsPerFifo = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterDeallocation = 0;
  parameter int DataRamAddressDepthStages = 0;
  parameter int PointerRamAddressDepthStages = 0;

  localparam int FifoIdWidth = $clog2(NumFifos);

  logic clk;
  logic rst;
  logic start;
  logic finished;
  logic [31:0] error_count;

  logic [NumWritePorts-1:0] push_ready;
  logic [NumWritePorts-1:0] push_valid;
  logic [NumWritePorts-1:0][Width-1:0] push_data;
  logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id;

  logic [NumFifos-1:0] pop_ready;
  logic [NumFifos-1:0] pop_valid;
  logic [NumFifos-1:0][Width-1:0] pop_data;

  br_fifo_shared_dynamic_flops #(
      .NumFifos(NumFifos),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .NumLinkedListsPerFifo(NumLinkedListsPerFifo),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation),
      .DataRamAddressDepthStages(DataRamAddressDepthStages),
      .PointerRamAddressDepthStages(PointerRamAddressDepthStages)
  ) dut (
      .clk,
      .rst,
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
      .NumWritePorts(NumWritePorts),
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

    td.reset_dut();
    td.wait_cycles(10);

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
