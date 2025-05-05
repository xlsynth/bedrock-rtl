module br_fifo_shared_pstatic_flops_push_credit_tb;
  parameter int MaxRandomDelay = 4;
  parameter int TestSize = 1000;
  parameter int NumFifos = 2;
  parameter int Depth = 8;
  parameter int Width = 8;
  parameter int StagingBufferDepth = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterPushOutputs = 0;
  parameter int RamAddressDepthStages = 0;

  localparam int FifoIdWidth = $clog2(NumFifos);
  localparam int CountWidth = $clog2(Depth + 1);
  localparam int AddrWidth = $clog2(Depth);

  logic                                   clk;
  logic                                   rst;
  logic                                   start;
  logic                                   finished;
  logic [           31:0]                 error_count;

  logic                                   push_ready;
  logic                                   push_valid;
  logic [      Width-1:0]                 push_data;
  logic [FifoIdWidth-1:0]                 push_fifo_id;

  logic [   NumFifos-1:0]                 sender_push_valid;
  logic [   NumFifos-1:0]                 sender_push_ready;
  logic [   NumFifos-1:0][     Width-1:0] sender_push_data;
  logic [   NumFifos-1:0][CountWidth-1:0] credit_initial_sender;
  logic [   NumFifos-1:0][CountWidth-1:0] credit_withhold_sender;

  logic [   NumFifos-1:0]                 sender_request;
  logic [   NumFifos-1:0]                 sender_can_grant;
  logic [   NumFifos-1:0]                 sender_grant;
  logic                                   sender_enable_priority_update;

  logic                                   dut_push_sender_in_reset;
  logic                                   dut_push_receiver_in_reset;
  logic [   NumFifos-1:0]                 dut_push_credit;
  logic                                   dut_push_valid;
  logic [      Width-1:0]                 dut_push_data;
  logic [FifoIdWidth-1:0]                 dut_push_fifo_id;
  logic [   NumFifos-1:0][CountWidth-1:0] credit_initial_push;
  logic [   NumFifos-1:0][CountWidth-1:0] credit_withhold_push;

  assign credit_initial_sender = '0;
  assign credit_withhold_sender = '0;
  assign credit_initial_push = '{default: CountWidth'(Depth / NumFifos)};
  assign credit_withhold_push = '0;

  br_flow_demux_select_unstable #(
      .NumFlows(NumFifos),
      .Width(Width)
  ) br_flow_demux_select_unstable_push (
      .clk,
      .rst,
      .select(push_fifo_id),
      .push_valid,
      .push_ready,
      .push_data,
      .pop_valid_unstable(sender_push_valid),
      .pop_ready(sender_push_ready),
      .pop_data_unstable(sender_push_data)
  );

  br_credit_sender_vc #(
      .NumVcs(NumFifos),
      .RegisterPopOutputs(1),
      .MaxCredit(Depth),
      .Width(Width)
  ) br_credit_sender_vc_push (
      .clk,
      .rst,
      .request(sender_request),
      .can_grant(sender_can_grant),
      .grant(sender_grant),
      .enable_priority_update(sender_enable_priority_update),
      .push_valid(sender_push_valid),
      .push_ready(sender_push_ready),
      .push_data(sender_push_data),
      .pop_valid(dut_push_valid),
      .pop_credit(dut_push_credit),
      .pop_data(dut_push_data),
      .pop_vc(dut_push_fifo_id),
      .pop_sender_in_reset(dut_push_sender_in_reset),
      .pop_receiver_in_reset(dut_push_receiver_in_reset),
      .credit_initial(credit_initial_sender),
      .credit_withhold(credit_withhold_sender),
      .credit_count(),
      .credit_available()
  );

  br_arb_rr_internal #(
      .NumRequesters(NumFifos)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .request(sender_request),
      .can_grant(sender_can_grant),
      .grant(sender_grant),
      .enable_priority_update(sender_enable_priority_update)
  );

  logic [NumFifos-1:0][AddrWidth-1:0] config_base;
  logic [NumFifos-1:0][AddrWidth-1:0] config_bound;
  logic config_error;

  logic [NumFifos-1:0] pop_ready;
  logic [NumFifos-1:0] pop_valid;
  logic [NumFifos-1:0][Width-1:0] pop_data;

  br_fifo_shared_pstatic_flops_push_credit #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RamAddressDepthStages(RamAddressDepthStages)
  ) dut (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
      .push_sender_in_reset(dut_push_sender_in_reset),
      .push_receiver_in_reset(dut_push_receiver_in_reset),
      .push_credit_stall('0),
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
