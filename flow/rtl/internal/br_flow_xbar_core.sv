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

// Bedrock-RTL Flow-Controlled Crossbar Core

`include "br_asserts_internal.svh"

module br_flow_xbar_core #(
    parameter int NumPushFlows = 2,
    parameter int NumPopFlows = 2,
    parameter int Width = 1,
    parameter bit RegisterDemuxOutputs = 0,
    parameter bit RegisterPopOutputs = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPushDestinationStability = EnableAssertPushDataStability,
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int DestIdWidth = $clog2(NumPopFlows)
) (
    input logic clk,
    input logic rst,

    // External-facing ports
    output logic [NumPushFlows-1:0] push_ready,
    input logic [NumPushFlows-1:0] push_valid,
    input logic [NumPushFlows-1:0][Width-1:0] push_data,
    input logic [NumPushFlows-1:0][DestIdWidth-1:0] push_dest_id,

    input logic [NumPopFlows-1:0] pop_ready,
    output logic [NumPopFlows-1:0] pop_valid,
    output logic [NumPopFlows-1:0][Width-1:0] pop_data,

    // Internal-facing ports
    output logic [NumPopFlows-1:0][NumPushFlows-1:0] request,
    input logic [NumPopFlows-1:0][NumPushFlows-1:0] can_grant,
    input logic [NumPopFlows-1:0][NumPushFlows-1:0] grant,
    output logic [NumPopFlows-1:0] enable_priority_update
);

  //------------------------------------------
  // Integration Assertions
  //------------------------------------------
  for (genvar i = 0; i < NumPushFlows; i++) begin : gen_push_flow_checks
    if (EnableAssertPushDestinationStability) begin : gen_dest_stability_assert
      `BR_ASSERT_INTG(push_dest_id_stable_when_backpressured_a,
                      push_valid[i] && !push_ready[i] |=> push_valid[i] && $stable(push_dest_id[i]))
    end else begin : gen_dest_instability_cover
      `BR_COVER_INTG(push_dest_id_unstable_when_backpressured_c,
                     ##1 $past(push_valid[i] && !push_ready[i]) && !$stable(push_dest_id[i]))
    end
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [NumPushFlows-1:0][NumPopFlows-1:0] demux_out_valid;
  logic [NumPushFlows-1:0][NumPopFlows-1:0] demux_out_ready;
  logic [NumPushFlows-1:0][NumPopFlows-1:0][Width-1:0] demux_out_data;

  logic [NumPopFlows-1:0][NumPushFlows-1:0] mux_in_valid;
  logic [NumPopFlows-1:0][NumPushFlows-1:0] mux_in_ready;
  logic [NumPopFlows-1:0][NumPushFlows-1:0][Width-1:0] mux_in_data;

  logic [NumPopFlows-1:0] mux_out_valid;
  logic [NumPopFlows-1:0] mux_out_ready;
  logic [NumPopFlows-1:0][Width-1:0] mux_out_data;

  for (genvar i = 0; i < NumPushFlows; i++) begin : gen_demux
    br_flow_demux_select_unstable #(
        .NumFlows(NumPopFlows),
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_demux_select_unstable_push (
        .clk,
        .rst,
        .push_valid(push_valid[i]),
        .push_ready(push_ready[i]),
        .push_data(push_data[i]),
        .select(push_dest_id[i]),
        .pop_ready(demux_out_ready[i]),
        .pop_valid_unstable(demux_out_valid[i]),
        .pop_data_unstable(demux_out_data[i])
    );

    for (genvar j = 0; j < NumPopFlows; j++) begin : gen_mux_input
      if (RegisterDemuxOutputs) begin : gen_reg_out
        br_flow_reg_fwd #(
            .Width(Width),
            .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
            .EnableAssertPushValidStability(
                EnableAssertPushValidStability && EnableAssertPushDestinationStability),
            .EnableAssertPushDataStability(
                EnableAssertPushDataStability && EnableAssertPushDestinationStability),
            .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
        ) br_flow_reg_fwd_demux_to_mux (
            .clk,
            .rst,
            .push_valid(demux_out_valid[i][j]),
            .push_ready(demux_out_ready[i][j]),
            .push_data (demux_out_data[i][j]),
            .pop_ready (mux_in_ready[j][i]),
            .pop_valid (mux_in_valid[j][i]),
            .pop_data  (mux_in_data[j][i])
        );
      end else begin : gen_no_reg_out
        assign mux_in_valid[j][i] = demux_out_valid[i][j];
        assign mux_in_data[j][i] = demux_out_data[i][j];
        assign demux_out_ready[i][j] = mux_in_ready[j][i];
      end
    end
  end

  for (genvar i = 0; i < NumPopFlows; i++) begin : gen_mux
    br_flow_mux_core #(
        .NumFlows(NumPushFlows),
        .Width(Width),
        // If demux outputs are registered, it is possible for
        // mux_in to be backpressured and mux_in_valid/data
        // must be stable.
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure || RegisterDemuxOutputs),
        .EnableAssertPushValidStability(
            (EnableAssertPushValidStability && EnableAssertPushDestinationStability) ||
            RegisterDemuxOutputs),
        .EnableAssertPushDataStability(
            (EnableAssertPushDataStability && EnableAssertPushDestinationStability) ||
            RegisterDemuxOutputs),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_mux_core_pop (
        .clk,
        .rst,
        .push_valid(mux_in_valid[i]),
        .push_ready(mux_in_ready[i]),
        .push_data(mux_in_data[i]),
        .pop_ready(mux_out_ready[i]),
        .pop_valid_unstable(mux_out_valid[i]),
        .pop_data_unstable(mux_out_data[i]),
        .request(request[i]),
        .can_grant(can_grant[i]),
        .grant(grant[i]),
        .enable_priority_update(enable_priority_update[i])
    );

    if (RegisterPopOutputs) begin : gen_reg_out
      br_flow_reg_fwd #(
          .Width(Width),
          .EnableCoverPushBackpressure(EnableCoverPushBackpressure || RegisterDemuxOutputs),
          .EnableAssertPushValidStability(
              (EnableAssertPushValidStability && EnableAssertPushDestinationStability) ||
              RegisterDemuxOutputs),
          // Push data cannot be stable because it comes from the arbiter
          .EnableAssertPushDataStability(0),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_flow_reg_fwd_mux_to_pop (
          .clk,
          .rst,
          .push_valid(mux_out_valid[i]),
          .push_ready(mux_out_ready[i]),
          .push_data (mux_out_data[i]),
          .pop_ready (pop_ready[i]),
          .pop_valid (pop_valid[i]),
          .pop_data  (pop_data[i])
      );
    end else begin : gen_no_reg_out
      assign pop_valid[i] = mux_out_valid[i];
      assign pop_data[i] = mux_out_data[i];
      assign mux_out_ready[i] = pop_ready[i];
    end
  end

  //------------------------------------------
  // Implementation Assertions
  //------------------------------------------
  // Rely on assertions in submodules

endmodule
