// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Crossbar Core

`include "br_asserts_internal.svh"

module br_flow_xbar_core #(
    parameter int NumPushFlows = 1,
    parameter int NumPopFlows = 1,
    parameter int Width = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int PushBufferDepth = 0,
    parameter bit PushBufferRegisterPushOutputs = (PushBufferDepth > 1),
    parameter bit PushBufferRegisterPopOutputs = 1,
    parameter int PathBufferDepth = 0,
    parameter bit PathBufferRegisterPushOutputs = (PathBufferDepth >= 3),
    parameter bit PathBufferRegisterPopOutputs = (PathBufferDepth > 0),
    parameter int PopBufferDepth = RegisterPopOutputs ? 1 : 0,
    parameter bit PopBufferRegisterPushOutputs = (PopBufferDepth > 1),
    parameter bit PopBufferRegisterPopOutputs = RegisterPopOutputs,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPushDestinationStability = EnableAssertPushDataStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    parameter bit EnableAssertFinalNotValid = 1,

    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    localparam int DestIdWidth = br_math::clamped_clog2(NumPopFlows)
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
  // Rely on assertions in submodules

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Optional input buffers
  localparam int PushPayloadWidth = Width + DestIdWidth;

  logic [NumPushFlows-1:0]                       push_buffer_ready;
  logic [NumPushFlows-1:0]                       push_buffer_valid;
  logic [NumPushFlows-1:0][PushPayloadWidth-1:0] push_buffer_payload;
  logic [NumPushFlows-1:0][           Width-1:0] push_buffer_data;
  logic [NumPushFlows-1:0][     DestIdWidth-1:0] push_buffer_dest_id;

  for (genvar i = 0; i < NumPushFlows; i++) begin : gen_push_buffer
    logic [PushPayloadWidth-1:0] push_payload;

    assign push_payload = {push_dest_id[i], push_data[i]};

    br_flow_buffer #(
        .Depth(PushBufferDepth),
        .Width(PushPayloadWidth),
        .RegisterPushOutputs(PushBufferRegisterPushOutputs),
        .RegisterPopOutputs(PushBufferRegisterPopOutputs),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        // The push buffer carries both data and destination as one payload.
        .EnableAssertPushDataStability(
            EnableAssertPushDataStability || EnableAssertPushDestinationStability),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_buffer_push (
        .clk,  // ri lint_check_waive CLOCK_USE
        .rst,
        .push_ready(push_ready[i]),
        .push_valid(push_valid[i]),
        .push_data (push_payload),
        .pop_ready (push_buffer_ready[i]),
        .pop_valid (push_buffer_valid[i]),
        .pop_data  (push_buffer_payload[i])
    );

    assign {push_buffer_dest_id[i], push_buffer_data[i]} = push_buffer_payload[i];
  end

  // Demux with optional per-path contention buffer
  logic [NumPushFlows-1:0][ NumPopFlows-1:0]            demux_out_valid;
  logic [NumPushFlows-1:0][ NumPopFlows-1:0]            demux_out_ready;
  logic [NumPushFlows-1:0][ NumPopFlows-1:0][Width-1:0] demux_out_data;

  logic [ NumPopFlows-1:0][NumPushFlows-1:0]            mux_in_valid;
  logic [ NumPopFlows-1:0][NumPushFlows-1:0]            mux_in_ready;
  logic [ NumPopFlows-1:0][NumPushFlows-1:0][Width-1:0] mux_in_data;

  for (genvar i = 0; i < NumPushFlows; i++) begin : gen_demux
    localparam bit PushBufferStabilizes = PushBufferDepth > 0;

    br_flow_demux_select_unstable #(
        .NumFlows(NumPopFlows),
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertNoPushBackpressure(PushBufferStabilizes ? 0 : EnableAssertNoPushBackpressure),
        .EnableAssertPushValidStability(
            EnableCoverPushBackpressure && (EnableAssertPushValidStability || PushBufferStabilizes)),
        .EnableAssertPushDataStability(
            EnableCoverPushBackpressure && (EnableAssertPushDataStability || PushBufferStabilizes)),
        .EnableAssertSelectStability(
            EnableCoverPushBackpressure &&
            (EnableAssertPushDestinationStability || PushBufferStabilizes)),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_demux_select_unstable_push (
        .clk,
        .rst,
        .push_valid(push_buffer_valid[i]),
        .push_ready(push_buffer_ready[i]),
        .push_data(push_buffer_data[i]),
        .select(push_buffer_dest_id[i]),
        .pop_ready(demux_out_ready[i]),
        .pop_valid_unstable(demux_out_valid[i]),
        .pop_data_unstable(demux_out_data[i])
    );

    for (genvar j = 0; j < NumPopFlows; j++) begin : gen_path_buffer
      br_flow_buffer #(
          .Depth(PathBufferDepth),
          .Width(Width),
          .RegisterPushOutputs(PathBufferRegisterPushOutputs),
          .RegisterPopOutputs(PathBufferRegisterPopOutputs),
          .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
          .EnableAssertNoPushBackpressure(0),
          .EnableAssertPushValidStability(
              EnableCoverPushBackpressure &&
              (EnableAssertPushValidStability && EnableAssertPushDestinationStability ||
               PushBufferStabilizes)),
          .EnableAssertPushDataStability(
              EnableCoverPushBackpressure &&
              (EnableAssertPushDataStability && EnableAssertPushDestinationStability ||
               PushBufferStabilizes)),
          .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_flow_buffer_path (
          .clk,  // ri lint_check_waive CLOCK_USE
          .rst,
          .push_valid(demux_out_valid[i][j]),
          .push_ready(demux_out_ready[i][j]),
          .push_data (demux_out_data[i][j]),
          .pop_ready (mux_in_ready[j][i]),
          .pop_valid (mux_in_valid[j][i]),
          .pop_data  (mux_in_data[j][i])
      );
    end
  end

  // Mux with optional output buffer
  logic [NumPopFlows-1:0]            mux_out_valid;
  logic [NumPopFlows-1:0]            mux_out_ready;
  logic [NumPopFlows-1:0][Width-1:0] mux_out_data;

  for (genvar i = 0; i < NumPopFlows; i++) begin : gen_mux
    localparam bit PushBufferStabilizes = PushBufferDepth > 0;
    localparam bit PathBufferStabilizes = PathBufferDepth > 0;

    br_flow_mux_core #(
        .NumFlows(NumPushFlows),
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertNoPushBackpressure(0),
        .EnableAssertPushValidStability(
            EnableCoverPushBackpressure &&
            (PathBufferStabilizes ||
             PushBufferStabilizes ||
             (EnableAssertPushValidStability && EnableAssertPushDestinationStability))),
        .EnableAssertPushDataStability(
            EnableCoverPushBackpressure &&
            (PathBufferStabilizes ||
             PushBufferStabilizes ||
             (EnableAssertPushDataStability && EnableAssertPushDestinationStability))),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
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

    br_flow_buffer #(
        .Depth(PopBufferDepth),
        .Width(Width),
        .RegisterPushOutputs(PopBufferRegisterPushOutputs),
        .RegisterPopOutputs(PopBufferRegisterPopOutputs),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertNoPushBackpressure(0),
        .EnableAssertPushValidStability(
            EnableCoverPushBackpressure &&
            (PathBufferStabilizes || PushBufferStabilizes || EnableAssertPushDestinationStability)),
        // Push data can change when the arbiter grant changes.
        .EnableAssertPushDataStability(0),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_buffer_pop (
        .clk,  // ri lint_check_waive CLOCK_USE
        .rst,
        .push_valid(mux_out_valid[i]),
        .push_ready(mux_out_ready[i]),
        .push_data (mux_out_data[i]),
        .pop_ready (pop_ready[i]),
        .pop_valid (pop_valid[i]),
        .pop_data  (pop_data[i])
    );
  end

  //------------------------------------------
  // Implementation Assertions
  //------------------------------------------
  // Rely on assertions in submodules

endmodule
