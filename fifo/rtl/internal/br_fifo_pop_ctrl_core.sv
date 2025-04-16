// Copyright 2024-2025 The Bedrock-RTL Authors
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

`include "br_asserts.svh"
`include "br_unused.svh"

module br_fifo_pop_ctrl_core #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    parameter int RamReadLatency = 0,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamDepth = Depth,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = br_math::clamped_clog2(RamDepth),
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
  // Integration Checks
  //------------------------------------------

  // If EnableBypass is 0, RamDepth must be at least the FIFO depth.
  // If EnableBypass is 1, the staging buffers may provide additional space,
  // so the RAM depth can be smaller than the FIFO depth.
  // ri lint_check_waive PARAM_NOT_USED
  localparam int StagingBufferDepth =
      (RamReadLatency == 0 && !RegisterPopOutputs) ? 0 : (RamReadLatency + 1);
  // ri lint_check_waive PARAM_NOT_USED
  localparam int MinRamDepth = EnableBypass ? br_math::max2(1, Depth - StagingBufferDepth) : Depth;
  `BR_ASSERT_STATIC(legal_ram_depth_a, RamDepth >= MinRamDepth)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Flow control
  assign pop_beat = pop_ready && pop_valid;

  // RAM path
  if (RamDepth > 1) begin : gen_ram_rd_addr_counter
    br_counter_incr #(
        .MaxValue(RamDepth - 1),
        .MaxIncrement(1),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
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
  end else begin : gen_ram_rd_addr_const
    assign ram_rd_addr = 1'b0;
  end

  // Datapath
  if (RamReadLatency == 0 && !RegisterPopOutputs) begin : gen_no_buffer
    if (EnableBypass) begin : gen_bypass
      assign bypass_ready = empty && pop_ready;
      assign pop_valid = !empty || bypass_valid_unstable;
      assign pop_data = empty ? bypass_data_unstable : ram_rd_data;
      assign ram_rd_addr_valid = pop_valid && pop_ready && !empty;
    end else begin : gen_no_bypass
      // TODO(zhemao, #157): Replace this with BR_TIEOFF macros once they are fixed
      assign bypass_ready = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
      assign pop_valid = !empty;
      assign pop_data = ram_rd_data;
      assign ram_rd_addr_valid = pop_valid && pop_ready;

      `BR_UNUSED_NAMED(bypass_signals, {bypass_valid_unstable, bypass_data_unstable})
    end
    `BR_UNUSED(ram_rd_data_valid)  // implied
    `BR_UNUSED(items)
  end else begin : gen_staging_buffer
    br_fifo_staging_buffer #(
        .EnableBypass             (EnableBypass),
        .TotalDepth               (Depth),
        .RamReadLatency           (RamReadLatency),
        .Width                    (Width),
        .RegisterPopOutputs       (RegisterPopOutputs),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_fifo_staging_buffer (
        .clk,
        .rst,

        // If bypass is disabled, bypass_ready will be driven by constant
        // TODO(zhemao, #157): Remove this once lint waiver issue is fixed
        .bypass_ready,  // ri lint_check_waive CONST_OUTPUT
        .bypass_valid_unstable,
        .bypass_data_unstable,

        .total_items(items),

        .ram_rd_addr_ready(1'b1),
        .ram_rd_addr_valid,
        .ram_rd_data_valid,
        .ram_rd_data,

        .pop_ready,
        .pop_valid,
        .pop_data,
        .pop_empty()
    );
    `BR_UNUSED(empty)
  end

endmodule : br_fifo_pop_ctrl_core
