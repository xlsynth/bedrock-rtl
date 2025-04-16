module br_fifo_shared_dynamic_flops_push_credit_tb;
  parameter int MaxRandomDelay = 4;
  parameter int TestSize = 1000;
  parameter int NumFifos = 2;
  parameter int NumWritePorts = 1;
  parameter int NumReadPorts = 1;
  parameter int Depth = 5;
  parameter int Width = 8;
  parameter int StagingBufferDepth = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterDeallocation = 0;
  parameter int DataRamAddressDepthStages = 0;
  parameter int PointerRamAddressDepthStages = 0;

  localparam int FifoIdWidth = $clog2(NumFifos);
  localparam int CombinedWidth = Width + FifoIdWidth;
  localparam int PushCreditWidth = $clog2(NumWritePorts + 1);
  localparam int CountWidth = $clog2(Depth + 1);

  logic clk;
  logic rst;
  logic start;
  logic finished;
  logic [31:0] error_count;

  logic [NumWritePorts-1:0] push_ready;
  logic [NumWritePorts-1:0] push_valid;
  logic [NumWritePorts-1:0][Width-1:0] push_data;
  logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id;
  logic [NumWritePorts-1:0][CombinedWidth-1:0] push_data_comb;
  logic [CountWidth-1:0] credit_initial_sender;
  logic [CountWidth-1:0] credit_withhold_sender;

  logic dut_push_sender_in_reset;
  logic dut_push_receiver_in_reset;
  logic [PushCreditWidth-1:0] dut_push_credit;
  logic [NumWritePorts-1:0] dut_push_valid;
  logic [NumWritePorts-1:0][Width-1:0] dut_push_data;
  logic [NumWritePorts-1:0][CombinedWidth-1:0] dut_push_data_comb;
  logic [NumWritePorts-1:0][FifoIdWidth-1:0] dut_push_fifo_id;
  logic [CountWidth-1:0] credit_initial_push;
  logic [CountWidth-1:0] credit_withhold_push;

  assign credit_initial_sender = '0;
  assign credit_withhold_sender = '0;
  assign credit_initial_push = Depth;
  assign credit_withhold_push = '0;

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_push_data_comb
    assign push_data_comb[i] = {push_fifo_id[i], push_data[i]};
    assign {dut_push_fifo_id[i], dut_push_data[i]} = dut_push_data_comb[i];
  end

  br_credit_sender #(
      .NumFlows(NumWritePorts),
      .PopCreditMaxChange(NumWritePorts),
      .RegisterPopOutputs(RegisterPopOutputs),
      .MaxCredit(Depth),
      .Width(CombinedWidth)
  ) br_credit_sender_push (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data(push_data_comb),
      .pop_valid(dut_push_valid),
      .pop_credit(dut_push_credit),
      .pop_data(dut_push_data_comb),
      .pop_sender_in_reset(dut_push_sender_in_reset),
      .pop_receiver_in_reset(dut_push_receiver_in_reset),
      .credit_initial(credit_initial_sender),
      .credit_withhold(credit_withhold_sender),
      .credit_count(),
      .credit_available()
  );

  logic [NumFifos-1:0] pop_ready;
  logic [NumFifos-1:0] pop_valid;
  logic [NumFifos-1:0][Width-1:0] pop_data;

  br_fifo_shared_dynamic_flops_push_credit #(
      .NumFifos(NumFifos),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation),
      .RegisterPushOutputs(1),
      .DataRamAddressDepthStages(DataRamAddressDepthStages),
      .PointerRamAddressDepthStages(PointerRamAddressDepthStages)
  ) dut (
      .clk,
      .rst,
      .push_sender_in_reset(dut_push_sender_in_reset),
      .push_receiver_in_reset(dut_push_receiver_in_reset),
      .push_credit_stall(1'b0),
      .push_credit(dut_push_credit),
      .push_valid(dut_push_valid),
      .push_data(dut_push_data),
      .push_fifo_id(dut_push_fifo_id),
      .push_full(),
      .credit_initial_push,
      .credit_withhold_push,
      .credit_available_push(),
      .credit_count_push(),
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
