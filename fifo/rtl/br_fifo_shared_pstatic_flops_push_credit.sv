// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_fifo_shared_pstatic_flops_push_credit #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than or equal to the number of logical FIFOs.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // If 1, register is added on the credit returns,
    // improving timing at the cost of additional latency.
    parameter bit RegisterPushOutputs = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `StagingBufferDepth / (PointerRamReadLatency + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // Number of tiles in the depth dimension for the flop RAM.
    parameter int RamDepthTiles = 1,
    // Number of tiles in the width dimension for the flop RAM.
    parameter int RamWidthTiles = 1,
    // Number of stages on the address path for the flop RAM.
    parameter int RamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the flop RAM.
    parameter int RamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the flop RAM.
    parameter int RamReadDataWidthStages = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth),
    localparam int CountWidth  = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Fifo configuration
    // These can come from straps or CSRs, but they must be set before reset is
    // deasserted and then held stable until reset is asserted.
    // The base and bound addresses determine the range of RAM addresses given
    // to each logical FIFO. They are both inclusive, so logical FIFO i will
    // increment from config_base[i] up to config_bound[i] before wrapping back
    // around to config_base[i] again.
    // The minimum size for a given logical FIFO is 1, meaning that
    // config_bound[i] must be >= config_base[i] for all i.
    // The address ranges must be in ascending order.
    input logic [NumFifos-1:0][AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][AddrWidth-1:0] config_bound,
    // Error is asserted if the base and bound addresses are misconfigured.
    // For instance, if any address is >= Depth, config_base[i] > config_bound[i],
    // or config_base[i] <= config_bound[i-1] for i > 0.
    output logic config_error,

    // Push-side interface
    input  logic                   push_sender_in_reset,
    output logic                   push_receiver_in_reset,
    input  logic [   NumFifos-1:0] push_credit_stall,
    output logic [   NumFifos-1:0] push_credit,
    input  logic                   push_valid,
    input  logic [      Width-1:0] push_data,
    input  logic [FifoIdWidth-1:0] push_fifo_id,
    output logic [   NumFifos-1:0] push_full,

    input  logic [NumFifos-1:0][CountWidth-1:0] credit_initial_push,
    input  logic [NumFifos-1:0][CountWidth-1:0] credit_withhold_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_available_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_count_push,

    // Pop-side interface
    input  logic [NumFifos-1:0]            pop_ready,
    output logic [NumFifos-1:0]            pop_valid,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0]            pop_empty
);

  // Integration assertions
  `BR_ASSERT_STATIC(num_fifos_gte_2_a, NumFifos >= 2)
  `BR_ASSERT_STATIC(depth_gte_num_fifos_a, Depth >= NumFifos)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)
  // Other integration checks in submodules

  // RAM read/write ports
  logic ram_wr_valid;
  logic [AddrWidth-1:0] ram_wr_addr;
  logic [Width-1:0] ram_wr_data;
  logic ram_rd_addr_valid;
  logic [AddrWidth-1:0] ram_rd_addr;
  logic ram_rd_data_valid;
  logic [Width-1:0] ram_rd_data;

  br_ram_flops #(
      .Width(Width),
      .Depth(Depth),
      .DepthTiles(RamDepthTiles),
      .WidthTiles(RamWidthTiles),
      .AddressDepthStages(RamAddressDepthStages),
      .ReadDataDepthStages(RamReadDataDepthStages),
      .ReadDataWidthStages(RamReadDataWidthStages)
  ) br_ram_flops_data (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(ram_wr_valid),
      .wr_addr(ram_wr_addr),
      .wr_data(ram_wr_data),
      .wr_word_en({RamWidthTiles{1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(ram_rd_addr_valid),
      .rd_addr(ram_rd_addr),
      .rd_data_valid(ram_rd_data_valid),
      .rd_data(ram_rd_data)
  );

  localparam int RamReadLatency =
      RamAddressDepthStages + RamReadDataDepthStages + RamReadDataWidthStages;

  br_fifo_shared_pstatic_ctrl_push_credit #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_pstatic_ctrl_push_credit (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
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
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data
  );

endmodule
