// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Shared Dynamic Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface) FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_flops_push_credit_fpv_monitor #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterPushOutputs = 0,
    parameter bit EnableCoverPushCreditStall = 1,
    parameter bit EnableCoverCreditWithhold = 1,
    parameter bit EnableCoverPushSenderInReset = 1,
    parameter bit RegisterDeallocation = 0,
    parameter int DataRamDepthTiles = 1,
    parameter int DataRamWidthTiles = 1,
    parameter int DataRamAddressDepthStages = 0,
    parameter int DataRamReadDataDepthStages = 0,
    parameter int DataRamReadDataWidthStages = 0,
    parameter int PointerRamDepthTiles = 1,
    parameter int PointerRamWidthTiles = 1,
    parameter int PointerRamAddressDepthStages = 0,
    parameter int PointerRamReadDataDepthStages = 0,
    parameter int PointerRamReadDataWidthStages = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Push side
    input logic push_sender_in_reset,
    input logic push_receiver_in_reset,
    input logic push_credit_stall,
    input logic [PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,

    input logic [CountWidth-1:0] credit_initial_push,
    input logic [CountWidth-1:0] credit_withhold_push,
    input logic [CountWidth-1:0] credit_available_push,
    input logic [CountWidth-1:0] credit_count_push,

    // Pop side
    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data
);

  localparam bit WolperColorEn = 0;
  logic [$clog2(Width)-1:0] magic_bit_index;
  `BR_ASSUME(magic_bit_index_range_a, $stable(magic_bit_index) && (magic_bit_index < Width))

  // ----------Instantiate credit FV checker----------
  br_credit_receiver_fpv_monitor #(
      .PStatic(0),
      .MaxCredit(Depth),
      .NumWritePorts(NumWritePorts),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall)
  ) fv_credit (
      .clk,
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .config_base ('d0),
      .config_bound('d0)
  );

  // ----------FIFO basic checks----------
  localparam int DataRamReadLatency =
      DataRamAddressDepthStages + DataRamReadDataDepthStages + DataRamReadDataWidthStages;
  localparam bit HasStagingBuffer = (DataRamReadLatency > 0) || RegisterPopOutputs;

  br_fifo_shared_dynamic_basic_fpv_monitor #(
      .WolperColorEn(WolperColorEn),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .HasStagingBuffer(HasStagingBuffer),
      .EnableCoverPushBackpressure(0)
  ) fv_checker (
      .clk,
      .rst,
      .push_valid,
      .push_ready({NumWritePorts{1'b1}}),
      .push_data,
      .push_fifo_id,
      .pop_valid,
      .pop_ready,
      .pop_data
  );

endmodule : br_fifo_shared_dynamic_flops_push_credit_fpv_monitor

bind br_fifo_shared_dynamic_flops_push_credit
     br_fifo_shared_dynamic_flops_push_credit_fpv_monitor #(
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RegisterPushOutputs(RegisterPushOutputs),
    .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
    .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
    .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
    .RegisterDeallocation(RegisterDeallocation),
    .DataRamDepthTiles(DataRamDepthTiles),
    .DataRamWidthTiles(DataRamWidthTiles),
    .DataRamAddressDepthStages(DataRamAddressDepthStages),
    .DataRamReadDataDepthStages(DataRamReadDataDepthStages),
    .DataRamReadDataWidthStages(DataRamReadDataWidthStages),
    .PointerRamDepthTiles(PointerRamDepthTiles),
    .PointerRamWidthTiles(PointerRamWidthTiles),
    .PointerRamAddressDepthStages(PointerRamAddressDepthStages),
    .PointerRamReadDataDepthStages(PointerRamReadDataDepthStages),
    .PointerRamReadDataWidthStages(PointerRamReadDataWidthStages),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
