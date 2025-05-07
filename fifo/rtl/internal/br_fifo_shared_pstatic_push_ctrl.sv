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
//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO Push Controller
//
// This module implements the push-side of a pseudo-static multi-FIFO.
// It tracks NumFifos write pointers that wrap around in dedicated ranges.
// TODO(zhemao): Support for multiple write ports.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_pstatic_push_ctrl #(
    // Number of logical FIFOs
    parameter int NumFifos = 2,
    // Total depth of the FIFO
    parameter int Depth = 3,
    // Width of the data
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Circular buffer base and bound for each logical FIFO.
    input logic [NumFifos-1:0][AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][AddrWidth-1:0] config_bound,

    // Push side
    output logic push_ready,
    input logic push_valid,
    input logic [Width-1:0] push_data,
    input logic [FifoIdWidth-1:0] push_fifo_id,
    input logic [NumFifos-1:0] push_full,

    // Data RAM write ports
    output logic ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [Width-1:0] ram_wr_data,

    // Write pointer to pointer manager
    output logic [NumFifos-1:0] advance_tail,
    output logic [NumFifos-1:0][AddrWidth-1:0] tail_next,
    output logic [NumFifos-1:0][AddrWidth-1:0] tail
);

  // Integration Assertions

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  logic [Width+FifoIdWidth-1:0] push_comb_data;

  assign push_comb_data = {push_fifo_id, push_data};

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(Width + FifoIdWidth),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg_inst (
      .clk,
      .rst,
      .valid(push_valid),
      .ready(push_ready),
      .data (push_comb_data)
  );

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  // Implementation
  logic [NumFifos-1:0] core_push_ready;
  logic [NumFifos-1:0] core_push_valid;
  logic [NumFifos-1:0][Width-1:0] core_push_data;
  logic [NumFifos-1:0] core_ram_wr_valid;
  logic [NumFifos-1:0][AddrWidth-1:0] core_ram_wr_addr;
  logic [NumFifos-1:0][Width-1:0] core_ram_wr_data;

  for (genvar i = 0; i < NumFifos; i++) begin : gen_ctrl_core
    assign advance_tail[i] = core_ram_wr_valid[i];
    assign tail[i] = core_ram_wr_addr[i];

    br_fifo_push_ctrl_core #(
        .Depth(Depth),
        .Width(Width),
        // TODO(zhemao): Add bypass support.
        .EnableBypass(0),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_fifo_push_ctrl_core_inst (
        .clk,
        .rst,
        .push_ready(core_push_ready[i]),
        .push_valid(core_push_valid[i]),
        .push_data(core_push_data[i]),
        .bypass_ready(1'b0),
        .bypass_valid_unstable(),
        .bypass_data_unstable(),
        .ram_wr_valid(core_ram_wr_valid[i]),
        .ram_wr_addr_next(tail_next[i]),
        .ram_wr_addr(core_ram_wr_addr[i]),
        .ram_wr_data(core_ram_wr_data[i]),
        .addr_base(config_base[i]),
        .addr_bound(config_bound[i]),
        .full(push_full[i]),
        .push_beat()
    );
  end

  br_flow_demux_select_unstable #(
      .NumFlows(NumFifos),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_demux_select_unstable_inst (
      .clk,
      .rst,
      .select(push_fifo_id),
      .push_ready,
      .push_valid,
      .push_data(push_data),
      .pop_ready(core_push_ready),
      .pop_valid_unstable(core_push_valid),
      .pop_data_unstable(core_push_data)
  );

  assign ram_wr_valid = |core_ram_wr_valid;

  br_mux_onehot #(
      .NumSymbolsIn(NumFifos),
      .SymbolWidth (AddrWidth)
  ) br_mux_onehot_ram_wr_addr (
      .select(core_ram_wr_valid),
      .in(core_ram_wr_addr),
      .out(ram_wr_addr)
  );

  br_mux_onehot #(
      .NumSymbolsIn(NumFifos),
      .SymbolWidth (Width)
  ) br_mux_onehot_ram_wr_data (
      .select(core_ram_wr_valid),
      .in(core_ram_wr_data),
      .out(ram_wr_data)
  );

endmodule
