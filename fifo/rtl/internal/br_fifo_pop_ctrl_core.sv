// Copyright 2024 The Bedrock-RTL Authors
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

// Core FIFO pop control logic that will be reused across different variants.
// Contains just the bypass and RAM read logic, leaving occupancy tracking up to
// the instantiating module.

`include "br_unused.svh"

module br_fifo_pop_ctrl_core #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    parameter int RamReadLatency = 0,
    parameter bit RegisterPopOutputs = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Pop-side interface.
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waivers.
    output logic bypass_ready,
    input logic bypass_valid_unstable,  // ri lint_check_waive INEFFECTIVE_NET
    input logic [Width-1:0] bypass_data_unstable,  // ri lint_check_waive INEFFECTIVE_NET

    // RAM interface
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    input  logic                 ram_rd_data_valid,  // ri lint_check_waive INEFFECTIVE_NET
    input  logic [    Width-1:0] ram_rd_data,

    input  logic                  empty,    // ri lint_check_waive INEFFECTIVE_NET
    input  logic [CountWidth-1:0] items,    // ri lint_check_waive INEFFECTIVE_NET
    output logic                  pop_beat
);

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Flow control
  assign pop_beat = pop_ready && pop_valid;

  // RAM path
  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_rd_addr (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(AddrWidth'(1'b0)),
      .incr_valid(ram_rd_addr_valid),
      .incr(1'b1),
      .value(ram_rd_addr),
      .value_next()  // unused
  );

  // Datapath
  if (RamReadLatency == 0) begin : gen_zero_rd_lat
    logic             internal_pop_valid;
    logic             internal_pop_ready;
    logic [Width-1:0] internal_pop_data;
    logic             internal_empty;

    if (EnableBypass) begin : gen_bypass
      assign bypass_ready = internal_empty && internal_pop_ready;
      assign internal_pop_valid = !internal_empty || bypass_valid_unstable;
      assign internal_pop_data = internal_empty ? bypass_data_unstable : ram_rd_data;
      assign ram_rd_addr_valid = internal_pop_valid && internal_pop_ready && !internal_empty;
    end else begin : gen_no_bypass
      // TODO(zhemao, #157): Replace this with BR_TIEOFF macros once they are fixed
      assign bypass_ready = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
      assign internal_pop_valid = !internal_empty;
      assign internal_pop_data = ram_rd_data;
      assign ram_rd_addr_valid = internal_pop_valid && internal_pop_ready;

      `BR_UNUSED_NAMED(bypass_signals, {bypass_valid_unstable, bypass_data_unstable})
    end
    `BR_UNUSED(ram_rd_data_valid)  // implied

    if (RegisterPopOutputs) begin : gen_reg_pop
      br_flow_reg_fwd #(
          .Width(Width)
      ) br_flow_reg_fwd_pop (
          .clk,
          .rst,
          .push_valid(internal_pop_valid),
          .push_ready(internal_pop_ready),
          .push_data (internal_pop_data),
          .pop_valid,
          .pop_ready,
          .pop_data
      );
      // internal_empty is true if there are no items or if there is one item
      // and it is already in the staging register
      assign internal_empty = empty || ((items == 1'b1) && pop_valid);
    end else begin : gen_noreg_pop
      assign internal_empty = empty;
      assign pop_valid = internal_pop_valid;
      assign pop_data = internal_pop_data;
      assign internal_pop_ready = pop_ready;
      `BR_UNUSED(items)
    end
  end else begin : gen_nonzero_rd_lat
    br_fifo_staging_buffer #(
        .EnableBypass      (EnableBypass),
        .TotalDepth        (Depth),
        .RamReadLatency    (RamReadLatency),
        .Width             (Width),
        .RegisterPopOutputs(RegisterPopOutputs)
    ) br_fifo_staging_buffer (
        .clk,
        .rst,

        // If bypass is disabled, bypass_ready will be driven by constant
        // TODO(zhemao, #157): Remove this once lint waiver issue is fixed
        .bypass_ready,  // ri lint_check_waive CONST_OUTPUT
        .bypass_valid_unstable,
        .bypass_data_unstable,

        .total_items(items),

        .ram_rd_addr_valid,
        .ram_rd_data_valid,
        .ram_rd_data,

        .pop_ready,
        .pop_valid,
        .pop_data
    );
    `BR_UNUSED(empty)
  end

endmodule : br_fifo_pop_ctrl_core
