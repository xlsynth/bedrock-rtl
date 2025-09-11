// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_pop_ctrl #(
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=1.
    parameter int NumFifos = 1,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `StagingBufferDepth / (PointerRamAddressDepthStages
    // + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int RamReadLatency = 0,

    localparam int AddrWidth  = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    output logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,
    input logic [NumFifos-1:0][CountWidth-1:0] ram_items,

    output logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0] pop_empty,

    output logic [NumFifos-1:0] dealloc_valid,
    output logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    output logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);

  logic [NumReadPorts-1:0][NumFifos-1:0] arb_request;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_can_grant;
  logic [NumReadPorts-1:0] arb_enable_priority_update;

  br_fifo_shared_pop_ctrl_ext_arbiter #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation),
      .RamReadLatency(RamReadLatency)
  ) br_fifo_shared_pop_ctrl_ext_arbiter (
      .clk,
      .rst,
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .ram_items,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .pop_empty,
      .dealloc_valid,
      .dealloc_entry_id,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .arb_request,
      .arb_grant,
      .arb_can_grant,
      .arb_enable_priority_update
  );

  for (genvar i = 0; i < NumReadPorts; i++) begin : gen_read_port_mux
    // Default arbitration policy is LRU. To use a different policy, use the _ext_arbiter variant.
    br_arb_lru_internal #(
        .NumRequesters(NumFifos)
    ) br_arb_lru_internal (
        .clk,
        .rst,
        .request(arb_request[i]),
        .can_grant(arb_can_grant[i]),
        .grant(arb_grant[i]),
        .enable_priority_update(arb_enable_priority_update[i])
    );
  end

endmodule
