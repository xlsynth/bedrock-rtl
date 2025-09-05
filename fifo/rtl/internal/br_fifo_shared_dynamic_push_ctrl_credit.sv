`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_fifo_shared_dynamic_push_ctrl_credit #(
    // Number of write ports
    parameter int NumWritePorts = 1,
    // Number of read ports.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs
    parameter int NumFifos = 1,
    // Total depth of the FIFO
    parameter int Depth = 3,
    // Width of the data
    parameter int Width = 1,
    // If 1, register the push credit return path, which adds an extra cycle
    // of round trip latency.
    parameter bit RegisterPushOutputs = 0,
    // If 1, cover that push_credit_stall can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushCreditStall = 1,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth),
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Push side
    input logic push_sender_in_reset,
    output logic push_receiver_in_reset,
    input logic push_credit_stall,
    output logic [PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    output logic push_full,

    input  logic [CountWidth-1:0] credit_initial_push,
    input  logic [CountWidth-1:0] credit_withhold_push,
    output logic [CountWidth-1:0] credit_available_push,
    output logic [CountWidth-1:0] credit_count_push,

    // Data RAM write ports
    output logic [NumWritePorts-1:0] data_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    output logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    // To Linked List Controllers
    output logic [NumFifos-1:0][NumWritePorts-1:0] next_tail_valid,
    output logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] next_tail,

    // Entry deallocation from pop controller
    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id
);
  logic either_rst;
  assign either_rst = push_sender_in_reset || rst;

  // Credit Receiver
  localparam int PopCreditMaxChange = br_math::min2(NumReadPorts, NumFifos);
  localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1);
  localparam int CombinedWidth = FifoIdWidth + Width;

  logic [PopCreditWidth-1:0] pop_credit;
  logic [NumWritePorts-1:0][CombinedWidth-1:0] push_data_comb;
  logic [NumWritePorts-1:0] internal_push_valid;
  logic [NumWritePorts-1:0][Width-1:0] internal_push_data;
  logic [NumWritePorts-1:0][FifoIdWidth-1:0] internal_push_fifo_id;
  logic [NumWritePorts-1:0][CombinedWidth-1:0] internal_push_data_comb;

  // Combine the FIFO ID and data per port into a single signal
  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_push_data_comb
    assign push_data_comb[i] = {push_fifo_id[i], push_data[i]};
    assign {internal_push_fifo_id[i], internal_push_data[i]} = internal_push_data_comb[i];
  end

  // Because there is a staging buffer in the freelist, the first
  // entry isn't available to be allocated until one cycle after
  // reset. If credit return isn't registered, we need to stall
  // credit return until allocation is available.
  localparam int InitialCreditDelay = 1 - RegisterPushOutputs;
  logic internal_push_credit_stall;

  if (InitialCreditDelay > 0) begin : gen_initial_credit_delay
    logic delayed_rst;

    br_delay_nr #(
        .NumStages(InitialCreditDelay),
        .Width(1)
    ) br_delay_nr_rst (
        .clk,
        .in(either_rst),
        .out(delayed_rst),
        .out_stages()
    );

    assign internal_push_credit_stall = push_credit_stall || delayed_rst;
  end else begin : gen_no_initial_credit_delay
    assign internal_push_credit_stall = push_credit_stall;
  end

  br_credit_receiver #(
      .NumFlows(NumWritePorts),
      .Width(CombinedWidth),
      .MaxCredit(Depth),
      .PushCreditMaxChange(NumWritePorts),
      .PopCreditMaxChange(PopCreditMaxChange),
      .RegisterPushOutputs(RegisterPushOutputs),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_credit_receiver (
      .clk,
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall(internal_push_credit_stall),
      .push_credit,
      .push_valid,
      .push_data(push_data_comb),
      .pop_credit,
      .pop_valid(internal_push_valid),
      .pop_data(internal_push_data_comb),
      .credit_initial(credit_initial_push),
      .credit_withhold(credit_withhold_push),
      .credit_available(credit_available_push),
      .credit_count(credit_count_push)
  );

  // Base Push Control
  localparam int DeallocCountWidth = $clog2(NumFifos + 1);
  logic [NumWritePorts-1:0] internal_push_ready;
  logic [DeallocCountWidth-1:0] dealloc_count;

  br_fifo_shared_dynamic_push_ctrl #(
      .NumWritePorts(NumWritePorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .DeallocCountDelay(2 - RegisterPushOutputs),
      .EnableCoverPushBackpressure(0),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_push_ctrl (
      .clk,
      .rst(either_rst),
      .push_valid(internal_push_valid),
      .push_ready(internal_push_ready),
      .push_data(internal_push_data),
      .push_fifo_id(internal_push_fifo_id),
      .push_full,
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .next_tail_valid,
      .next_tail,
      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_count
  );

  if (PopCreditWidth < DeallocCountWidth) begin : gen_trunc_pop_credit
    assign pop_credit = dealloc_count[PopCreditWidth-1:0];
    `BR_UNUSED_NAMED(dealloc_count_msb, dealloc_count[DeallocCountWidth-1:PopCreditWidth])
  end else begin : gen_no_trunc_pop_credit
    assign pop_credit = dealloc_count;
  end

  `BR_UNUSED(internal_push_ready)  // only used for assertions

  // Implementation Assertions
  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_wport_impl_asserts
    `BR_ASSERT_IMPL(no_internal_push_overflow_a, internal_push_valid[i] |-> internal_push_ready[i])
  end
  `BR_ASSERT_IMPL(dealloc_count_lte_max_pop_credit_a, dealloc_count <= PopCreditMaxChange)
endmodule
