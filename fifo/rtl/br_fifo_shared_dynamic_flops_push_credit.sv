// SPDX-License-Identifier: Apache-2.0

module br_fifo_shared_dynamic_flops_push_credit #(
    // Number of write ports. Must be >=1.
    parameter int NumWritePorts = 1,
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 3,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `StagingBufferDepth / (DataRamAddressDepthStages
    // + DataRamReadDataDepthStages + DataRamReadDataWidthStages + 1)`.
    parameter int StagingBufferDepth = 1,
    // The number of sub-linked lists used by each logical FIFO.
    // This affects the pop bandwidth of each logical FIFO.
    // The max bandwidth will be `NumLinkedListsPerFifo / (PointerRamReadLatency + 1)`.
    parameter int NumLinkedListsPerFifo = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, add a retiming stage to the push_credit signal so that it is
    // driven directly from a flop. This comes at the expense of one additional
    // cycle of credit loop latency.
    parameter bit RegisterPushOutputs = 0,
    // If 1, cover that push_credit_stall can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushCreditStall = 1,
    // If 1, cover that credit_withhold can be non-zero.
    // Otherwise, assert that it is always zero.
    parameter bit EnableCoverCreditWithhold = 1,
    // If 1, cover that push_sender_in_reset can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushSenderInReset = 1,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // Number of tiles in the depth dimension for the data flop RAM.
    parameter int DataRamDepthTiles = 1,
    // Number of tiles in the width dimension for the data flop RAM.
    parameter int DataRamWidthTiles = 1,
    // Number of stages on the address path for the data flop RAM.
    parameter int DataRamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the data flop RAM.
    parameter int DataRamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the data flop RAM.
    parameter int DataRamReadDataWidthStages = 0,
    // Number of tiles in the depth dimension for the pointer flop RAM.
    parameter int PointerRamDepthTiles = 1,
    // Number of tiles in the width dimension for the pointer flop RAM.
    parameter int PointerRamWidthTiles = 1,
    // Number of stages on the address path for the pointer flop RAM.
    parameter int PointerRamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the pointer flop RAM.
    parameter int PointerRamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the pointer flop RAM.
    parameter int PointerRamReadDataWidthStages = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
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

    // Pop side
    output logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0] pop_empty
);
  // Integration Checks
  // Rely on checks in the submodules

  // Implementation
  logic either_rst;
  assign either_rst = rst || push_sender_in_reset;

  // Data RAM
  logic [NumWritePorts-1:0] data_ram_wr_valid;
  logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr;
  logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data;

  logic [NumReadPorts-1:0] data_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr;
  logic [NumReadPorts-1:0] data_ram_rd_data_valid;
  logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .DepthTiles(DataRamDepthTiles),
      .WidthTiles(DataRamWidthTiles),
      .AddressDepthStages(DataRamAddressDepthStages),
      .ReadDataDepthStages(DataRamReadDataDepthStages),
      .ReadDataWidthStages(DataRamReadDataWidthStages)
  ) br_ram_flops_data (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(either_rst),
      .wr_valid(data_ram_wr_valid),
      .wr_addr(data_ram_wr_addr),
      .wr_data(data_ram_wr_data),
      .wr_word_en({(NumWritePorts * DataRamWidthTiles) {1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(either_rst),
      .rd_addr_valid(data_ram_rd_addr_valid),
      .rd_addr(data_ram_rd_addr),
      .rd_data_valid(data_ram_rd_data_valid),
      .rd_data(data_ram_rd_data)
  );

  // Pointer RAM
  logic [NumWritePorts-1:0] ptr_ram_wr_valid;
  logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr;
  logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data;

  logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr;
  logic [NumReadPorts-1:0] ptr_ram_rd_data_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(AddrWidth),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .DepthTiles(PointerRamDepthTiles),
      .WidthTiles(PointerRamWidthTiles),
      .AddressDepthStages(PointerRamAddressDepthStages),
      .ReadDataDepthStages(PointerRamReadDataDepthStages),
      .ReadDataWidthStages(PointerRamReadDataWidthStages)
  ) br_ram_flops_pointer (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(either_rst),
      .wr_valid(ptr_ram_wr_valid),
      .wr_addr(ptr_ram_wr_addr),
      .wr_data(ptr_ram_wr_data),
      .wr_word_en({(NumWritePorts * PointerRamWidthTiles) {1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(either_rst),
      .rd_addr_valid(ptr_ram_rd_addr_valid),
      .rd_addr(ptr_ram_rd_addr),
      .rd_data_valid(ptr_ram_rd_data_valid),
      .rd_data(ptr_ram_rd_data)
  );

  // Controller
  localparam int DataRamReadLatency =
      DataRamAddressDepthStages + DataRamReadDataDepthStages + DataRamReadDataWidthStages;
  localparam int PointerRamReadLatency =
      PointerRamAddressDepthStages + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages;

  br_fifo_shared_dynamic_ctrl_push_credit #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .NumLinkedListsPerFifo(NumLinkedListsPerFifo),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation),
      .DataRamReadLatency(DataRamReadLatency),
      .PointerRamReadLatency(PointerRamReadLatency),
      .RegisterPushOutputs(RegisterPushOutputs),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_ctrl (
      .clk,
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .push_fifo_id,
      .push_full,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_available_push,
      .credit_count_push,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .pop_empty,
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data
  );

  // Implementation Checks

  // Rely on implementation checks in the controller

endmodule : br_fifo_shared_dynamic_flops_push_credit
