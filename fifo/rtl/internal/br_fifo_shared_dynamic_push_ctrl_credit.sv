`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_fifo_shared_dynamic_push_ctrl_credit #(
    // Number of write ports
    parameter int NumWritePorts = 1,
    // Number of logical FIFOs
    parameter int NumFifos = 1,
    // Total depth of the FIFO
    parameter int Depth = 3,
    // Width of the data
    parameter int Width = 1,
    // If 1, register the push credit return path, which adds an extra cycle
    // of round trip latency.
    parameter bit RegisterPushOutputs = 0,
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

  // Credit Receiver
  localparam int PopCreditWidth = $clog2(NumFifos + 1);
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

  br_credit_receiver #(
      .NumFlows(NumWritePorts),
      .Width(CombinedWidth),
      .MaxCredit(Depth),
      .PushCreditMaxChange(NumWritePorts),
      .PopCreditMaxChange(NumFifos),
      .RegisterPushOutputs(RegisterPushOutputs),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_credit_receiver (
      .clk,
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
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
  logic [NumWritePorts-1:0] internal_push_ready;
  logic either_rst;

  assign either_rst = push_sender_in_reset || rst;

  br_fifo_shared_dynamic_push_ctrl #(
      .NumWritePorts(NumWritePorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .DeallocCountDelay(2 - RegisterPushOutputs),
      .EnableCoverPushBackpressure(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_push_ctrl (
      .clk,
      .rst(either_rst),
      .push_valid(internal_push_valid),
      .push_ready(internal_push_ready),
      .push_data(internal_push_data),
      .push_fifo_id(internal_push_fifo_id),
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .next_tail_valid,
      .next_tail,
      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_count(pop_credit)
  );

  `BR_UNUSED(internal_push_ready)  // only used for assertions

  // Implementation Assertions
  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_wport_impl_asserts
    `BR_ASSERT_IMPL(no_internal_push_overflow_a, internal_push_valid[i] |-> internal_push_ready[i])
  end
endmodule
