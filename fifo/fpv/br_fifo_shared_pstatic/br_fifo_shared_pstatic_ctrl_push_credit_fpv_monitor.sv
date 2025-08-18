// Copyright 2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL Shared Pseudo-Static Multi-FIFO Controller (Push Valid/Credit Interface)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pstatic_ctrl_push_credit_fpv_monitor #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than or equal to the number of logical FIFOs.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    parameter bit RegisterPushOutputs = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamReadLatency = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
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
    input logic config_error,

    // Push-side interface
    input logic                   push_sender_in_reset,
    input logic                   push_receiver_in_reset,
    input logic [   NumFifos-1:0] push_credit_stall,
    input logic [   NumFifos-1:0] push_credit,
    input logic                   push_valid,
    input logic [      Width-1:0] push_data,
    input logic [FifoIdWidth-1:0] push_fifo_id,
    input logic [   NumFifos-1:0] push_full,

    input logic [NumFifos-1:0][CountWidth-1:0] credit_initial_push,
    input logic [NumFifos-1:0][CountWidth-1:0] credit_withhold_push,
    input logic [NumFifos-1:0][CountWidth-1:0] credit_available_push,
    input logic [NumFifos-1:0][CountWidth-1:0] credit_count_push,

    // Pop-side interface
    input logic [NumFifos-1:0]            pop_ready,
    input logic [NumFifos-1:0]            pop_valid,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0]            pop_empty,

    // RAM read/write ports
    input logic                 ram_wr_valid,
    input logic [AddrWidth-1:0] ram_wr_addr,
    input logic [    Width-1:0] ram_wr_data,
    input logic                 ram_rd_addr_valid,
    input logic [AddrWidth-1:0] ram_rd_addr,
    input logic                 ram_rd_data_valid,
    input logic [    Width-1:0] ram_rd_data
);

  // ----------Instantiate credit FV checker----------
  for (genvar i = 0; i < NumFifos; i++) begin : gen_credit_checker
    br_credit_receiver_fpv_monitor #(
        .PStatic(1),
        .MaxCredit(Depth),
        .NumWritePorts(1)
    ) fv_credit (
        .clk,
        .rst,
        .push_sender_in_reset,
        .push_receiver_in_reset,
        .push_credit_stall(push_credit_stall[i]),
        .push_credit(push_credit[i]),
        .push_valid(push_valid && (push_fifo_id == i)),
        .credit_initial_push(credit_initial_push[i]),
        .credit_withhold_push(credit_withhold_push[i]),
        .credit_count_push(credit_count_push[i]),
        .credit_available_push(credit_available_push[i]),
        .config_base(config_base[i]),
        .config_bound(config_bound[i])
    );
  end

  // ----------Data Ram FV model----------
  br_fifo_fv_ram #(
      .NumWritePorts(1),
      .NumReadPorts(1),
      .Depth(Depth),
      .Width(Width),
      .RamReadLatency(RamReadLatency)
  ) fv_ram (
      .clk,
      .rst,
      .ram_wr_valid(ram_wr_valid),
      .ram_wr_addr(ram_wr_addr),
      .ram_wr_data(ram_wr_data),
      .ram_rd_addr_valid(ram_rd_addr_valid),
      .ram_rd_addr(ram_rd_addr),
      .ram_rd_data_valid(ram_rd_data_valid),
      .ram_rd_data(ram_rd_data)
  );

  // ----------FIFO basic checks----------
  br_fifo_shared_pstatic_basic_fpv_monitor #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .EnableCoverPushBackpressure(0)
  ) fv_checker (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
      .push_valid,
      .push_ready(1'b1),
      .push_data,
      .push_fifo_id,
      .push_full,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .pop_empty
  );

endmodule : br_fifo_shared_pstatic_ctrl_push_credit_fpv_monitor

bind br_fifo_shared_pstatic_ctrl_push_credit br_fifo_shared_pstatic_ctrl_push_credit_fpv_monitor #(
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .RegisterPushOutputs(RegisterPushOutputs),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RamReadLatency(RamReadLatency),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
