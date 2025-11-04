// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Shared Dynamic Multi-FIFO Controller (Push Valid/Ready Interface) FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_ctrl_push_credit_fpv_monitor #(
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
    // The bandwidth will be `StagingBufferDepth / (PointerRamReadLatency + 1)`.
    parameter int StagingBufferDepth = 1,
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
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int DataRamReadLatency = 0,
    // The number of cycles between pointer ram read address and read data. Must be >=0.
    parameter int PointerRamReadLatency = 0,
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
    input logic [NumFifos-1:0][Width-1:0] pop_data,

    // Data RAM Ports
    input logic [NumWritePorts-1:0] data_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    input logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,

    // Pointer RAM Ports
    input logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data,

    input logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr,
    input logic [NumReadPorts-1:0] ptr_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data
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

  // ----------Data Ram FV model----------
  br_fifo_fv_ram #(
      .WolperColorEn(WolperColorEn),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .RamReadLatency(DataRamReadLatency)
  ) fv_data_ram (
      .clk,
      .rst,
      .magic_bit_index(magic_bit_index),
      .ram_wr_valid(data_ram_wr_valid),
      .ram_wr_addr(data_ram_wr_addr),
      .ram_wr_data(data_ram_wr_data),
      .ram_rd_addr_valid(data_ram_rd_addr_valid),
      .ram_rd_addr(data_ram_rd_addr),
      .ram_rd_data_valid(data_ram_rd_data_valid),
      .ram_rd_data(data_ram_rd_data)
  );

  // ----------Ptr Ram FV model----------
  br_fifo_fv_ram #(
      .WolperColorEn(0),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(AddrWidth),
      .RamReadLatency(PointerRamReadLatency)
  ) fv_ptr_ram (
      .clk,
      .rst,
      .magic_bit_index('0),  // Not used
      .ram_wr_valid(ptr_ram_wr_valid),
      .ram_wr_addr(ptr_ram_wr_addr),
      .ram_wr_data(ptr_ram_wr_data),
      .ram_rd_addr_valid(ptr_ram_rd_addr_valid),
      .ram_rd_addr(ptr_ram_rd_addr),
      .ram_rd_data_valid(ptr_ram_rd_data_valid),
      .ram_rd_data(ptr_ram_rd_data)
  );

  // ----------FIFO basic checks----------
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

endmodule : br_fifo_shared_dynamic_ctrl_push_credit_fpv_monitor

bind br_fifo_shared_dynamic_ctrl_push_credit br_fifo_shared_dynamic_ctrl_push_credit_fpv_monitor #(
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
    .DataRamReadLatency(DataRamReadLatency),
    .PointerRamReadLatency(PointerRamReadLatency),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
