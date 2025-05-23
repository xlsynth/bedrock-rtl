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
// Bedrock-RTL AXI Demux Request Tracker
//
// This module is used to route the requests to the correct downstream port
// and to track on which downstream port the next response should arrive
// for each AXI ID.
//
// Implements a single-subordinate-per-ID tracking scheme. Transactions
// with the same ID may not be outstanding on multiple subordinates at the
// same time.
//
// Read response data interleaving is not supported.

`include "br_unused.svh"
`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_amba_axi_demux_req_tracker #(
    // Number of downstream subordinates.
    parameter int NumSubordinates = 2,
    // Width of the AXI ID field.
    parameter int AxiIdWidth = 1,
    // Maximum number of outstanding transactions per ID.
    parameter int MaxOutstandingPerId = 2,
    // Width of the request payload.
    parameter int ReqPayloadWidth = 1,
    // Width of the response payload.
    parameter int RespPayloadWidth = 1,
    // If 1, then only a single ID is supported.
    parameter int SingleIdOnly = 0,
    //
    localparam int SubIdWidth = $clog2(NumSubordinates)
) (
    input logic clk,
    input logic rst,

    // Upstream Request Interface (from manager)
    output logic upstream_axready,
    input logic upstream_axvalid,
    input logic [AxiIdWidth-1:0] upstream_axid,
    input logic [SubIdWidth-1:0] upstream_ax_sub_select,
    input logic [ReqPayloadWidth-1:0] upstream_ax_payload,

    // Downstream Request Interface (to subordinates)
    input logic [NumSubordinates-1:0] downstream_axready,
    output logic [NumSubordinates-1:0] downstream_axvalid,
    output logic [NumSubordinates-1:0][AxiIdWidth-1:0] downstream_axid,
    output logic [NumSubordinates-1:0][ReqPayloadWidth-1:0] downstream_ax_payload,

    // Upstream Response Interface (to manager)
    input logic upstream_xready,
    output logic upstream_xvalid,
    output logic [AxiIdWidth-1:0] upstream_xid,
    output logic upstream_xlast,
    output logic [RespPayloadWidth-1:0] upstream_x_payload,

    // Downstream Response Interface (from subordinates)
    output logic [NumSubordinates-1:0] downstream_xready,
    input logic [NumSubordinates-1:0] downstream_xvalid,
    input logic [NumSubordinates-1:0][AxiIdWidth-1:0] downstream_xid,
    input logic [NumSubordinates-1:0] downstream_xlast,
    input logic [NumSubordinates-1:0][RespPayloadWidth-1:0] downstream_x_payload,

    // WDATA flow control interface
    // A token is needed on this interface for each WDATA burst. When WDATA is not used
    // (i.e. for read requests), the wdata_flow_ready signal may be tied high.
    input logic wdata_flow_ready,
    output logic wdata_flow_valid,
    output logic [SubIdWidth-1:0] wdata_flow_sub_select
);

  localparam int NumIds = SingleIdOnly ? 1 : 2 ** AxiIdWidth;
  localparam int MaxOutstandingWidth = $clog2(MaxOutstandingPerId + 1);

  //
  // Integration checks
  //

  `BR_ASSERT_STATIC(num_subordinates_gte_2_a, NumSubordinates >= 2)
  `BR_ASSERT_STATIC(max_outstanding_per_id_gte_1_a, MaxOutstandingPerId >= 1)
  if (SingleIdOnly) begin : gen_single_id_only_checks
    `BR_ASSERT_INTG(axid_is_zero_a, upstream_axvalid |-> upstream_axid == '0)
    for (genvar i = 0; i < NumSubordinates; i++) begin : gen_subordinate_id_only_check
      `BR_ASSERT_INTG(xid_is_zero_a, downstream_xvalid[i] |-> downstream_xid[i] == '0)
    end
  end

  //
  // Internal signals
  //

  typedef struct packed {
    logic [ReqPayloadWidth-1:0] payload;
    logic [AxiIdWidth-1:0] id;
  } req_payload_t;

  typedef struct packed {
    logic [RespPayloadWidth-1:0] payload;
    logic [AxiIdWidth-1:0] id;
    logic last;
  } resp_payload_t;

  logic [SubIdWidth-1:0] upstream_ax_sub_select_int;
  req_payload_t upstream_ax_req_payload_int;
  logic upstream_axready_int;
  logic upstream_axvalid_int;

  req_payload_t [NumSubordinates-1:0] downstream_ax_req_payload;

  logic upstream_axready_reg;
  logic upstream_axvalid_reg;
  logic [AxiIdWidth-1:0] upstream_axid_reg;
  logic [SubIdWidth-1:0] upstream_ax_sub_select_reg;
  logic [ReqPayloadWidth-1:0] upstream_ax_payload_reg;

  logic resp_tracker_push_ready;
  logic resp_tracker_push_valid;

  logic [NumIds-1:0] resp_tracker_pop_ready_per_id;
  logic [NumIds-1:0] resp_tracker_pop_valid_per_id;
  logic [NumIds-1:0][SubIdWidth-1:0] resp_tracker_pop_sub_select_per_id;
  logic resp_tracker_pop_ready;

  //
  // Request Path
  //

  // Incoming request buffering (to cut upstream_ax_sub_select -> upstream_axready path)
  br_flow_reg_rev #(
      .Width(SubIdWidth + ReqPayloadWidth + AxiIdWidth)
  ) br_flow_reg_rev_upstream_req (
      .clk(clk),
      .rst(rst),
      //
      .push_ready(upstream_axready),
      .push_valid(upstream_axvalid),
      .push_data({upstream_axid, upstream_ax_sub_select, upstream_ax_payload}),
      //
      .pop_ready(upstream_axready_reg),
      .pop_valid(upstream_axvalid_reg),
      .pop_data({upstream_axid_reg, upstream_ax_sub_select_reg, upstream_ax_payload_reg})
  );

  // Fork into WDATA flow control interface and request tracking FIFO
  br_flow_fork #(
      .NumFlows(3)
  ) br_flow_fork_upstream_req (
      .clk(clk),
      .rst(rst),
      //
      .push_ready(upstream_axready_reg),
      .push_valid(upstream_axvalid_reg),
      //
      .pop_ready({wdata_flow_ready, resp_tracker_push_ready, upstream_axready_int}),
      .pop_valid_unstable({wdata_flow_valid, resp_tracker_push_valid, upstream_axvalid_int})
  );

  assign upstream_ax_sub_select_int = upstream_ax_sub_select_reg;
  assign upstream_ax_req_payload_int.id = upstream_axid_reg;
  assign upstream_ax_req_payload_int.payload = upstream_ax_payload_reg;

  assign wdata_flow_sub_select = upstream_ax_sub_select_reg;

  // Single-ID-per-port tracking
  // Transactions for a single ID may only be outstanding on a single port at a time. This is
  // required to avoid deadlock and is a similar strategy used in commercially-available AXI
  // interconnects.

  logic [NumIds-1:0][MaxOutstandingWidth-1:0] outstanding_per_id;
  logic [NumIds-1:0][SubIdWidth-1:0] active_port_per_id;
  logic [NumIds-1:0] resp_tracker_push_ready_per_id;
  logic [NumIds-1:0] resp_tracker_push_valid_per_id;

  for (genvar i = 0; i < NumIds; i++) begin : gen_track_port_outstanding_per_id
    logic zero_outstanding;
    logic update_active_port;

    assign zero_outstanding = (outstanding_per_id[i] == '0);

    // Accept if the the incoming request targets the same subordinate as currently outstanding
    // transactions for the same ID, or if there are no outstanding transactions for this ID.
    assign resp_tracker_push_ready_per_id[i] = upstream_axvalid_reg
                        && (outstanding_per_id[i] < MaxOutstandingPerId)
                        && ((upstream_ax_sub_select_reg == active_port_per_id[i])
                            || zero_outstanding);

    assign update_active_port = resp_tracker_push_ready_per_id[i] && zero_outstanding;
    `BR_REGL(active_port_per_id[i], upstream_ax_sub_select_reg, update_active_port)

    br_counter #(
        .MaxValue(MaxOutstandingPerId),
        .MaxChange(1),
        .EnableWrap(0),
        .EnableReinitAndChange(0),
        .EnableSaturate(0)
    ) br_counter_outstanding_per_id (
        .clk,
        .rst,
        //
        .reinit(1'b0),
        .initial_value('0),
        .incr_valid(resp_tracker_push_ready_per_id[i] && resp_tracker_push_valid_per_id[i]),
        .incr(1'b1),
        .decr_valid(resp_tracker_pop_valid_per_id[i] && resp_tracker_pop_ready_per_id[i]),
        .decr(1'b1),
        .value(outstanding_per_id[i]),
        .value_next()
    );

    assign resp_tracker_pop_valid_per_id[i] = outstanding_per_id[i] > 0;
    assign resp_tracker_pop_sub_select_per_id[i] = active_port_per_id[i];
  end

  if (SingleIdOnly) begin : gen_single_id_only_resp_tracker_push
    assign resp_tracker_push_ready = resp_tracker_push_ready_per_id;
    assign resp_tracker_push_valid_per_id = resp_tracker_push_valid;
  end else begin : gen_multi_id_resp_tracker_push
    logic [AxiIdWidth-1:0] resp_tracker_push_mux_select;
    assign resp_tracker_push_mux_select = upstream_axvalid_reg ? upstream_axid_reg : '0;

    br_flow_demux_select_unstable #(
        .NumFlows(NumIds),
        .Width(1),
        .EnableAssertPushValidStability(0)
    ) br_flow_demux_select_unstable_resp_tracker_push (
        .clk,
        .rst,
        //
        .select(resp_tracker_push_mux_select),
        //
        .push_ready(resp_tracker_push_ready),
        .push_valid(resp_tracker_push_valid),
        .push_data(1'b0),
        //
        .pop_ready(resp_tracker_push_ready_per_id),
        .pop_valid_unstable(resp_tracker_push_valid_per_id),
        .pop_data_unstable()
    );
  end

  // Request output demux
  logic [SubIdWidth-1:0] flow_demux_select;

  // Force select to a valid value if upstream_axvalid is low.
  assign flow_demux_select = upstream_axvalid_int ? upstream_ax_sub_select_int : '0;

  br_flow_demux_select_unstable #(
      .NumFlows(NumSubordinates),
      .Width(AxiIdWidth + ReqPayloadWidth)
  ) br_flow_demux_select_unstable_downstream_req (
      .clk(clk),
      .rst(rst),
      //
      .select(flow_demux_select),
      //
      .push_ready(upstream_axready_int),
      .push_valid(upstream_axvalid_int),
      .push_data(upstream_ax_req_payload_int),
      //
      .pop_ready(downstream_axready),
      .pop_valid_unstable(downstream_axvalid),
      .pop_data_unstable(downstream_ax_req_payload)
  );

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_ax_payload
    assign downstream_axid[i] = downstream_ax_req_payload[i].id;
    assign downstream_ax_payload[i] = downstream_ax_req_payload[i].payload;
  end

  //
  // Response Path
  //

  logic [NumSubordinates-1:0] downstream_xready_reg;
  logic [NumSubordinates-1:0] downstream_xvalid_reg;
  resp_payload_t [NumSubordinates-1:0] downstream_x_resp_payload_reg;

  logic upstream_xready_pre;
  logic upstream_xvalid_pre;
  resp_payload_t upstream_x_resp_payload_pre;

  // Buffer incoming responses to cut downstream_xvalid -> downstream_xready path
  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_buffer_resp
    br_flow_reg_rev #(
        .Width(AxiIdWidth + RespPayloadWidth + 1)
    ) br_flow_reg_rev_downstream_resp (
        .clk,
        .rst,
        //
        .push_ready(downstream_xready[i]),
        .push_valid(downstream_xvalid[i]),
        .push_data({downstream_xid[i], downstream_x_payload[i], downstream_xlast[i]}),
        //
        .pop_ready(downstream_xready_reg[i]),
        .pop_valid(downstream_xvalid_reg[i]),
        .pop_data({
          downstream_x_resp_payload_reg[i].id,
          downstream_x_resp_payload_reg[i].payload,
          downstream_x_resp_payload_reg[i].last
        })
    );
  end

  // Downstream port arbitration
  logic [NumSubordinates-1:0] ds_port_req;
  logic [NumSubordinates-1:0] ds_port_gnt;
  logic [NumSubordinates-1:0] ds_port_gnt_hold;
  logic [NumSubordinates-1:0] ds_port_id_match;

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_ds_port_id_match
    logic [SubIdWidth-1:0] next_port_for_id;
    logic next_port_for_id_valid;

    if (SingleIdOnly) begin : gen_single_id_only_no_pop_mux
      assign next_port_for_id = resp_tracker_pop_sub_select_per_id;
      assign next_port_for_id_valid = resp_tracker_pop_valid_per_id;
    end else begin : gen_multi_id_pop_mux
      logic [AxiIdWidth-1:0] mux_select;
      assign mux_select = downstream_xvalid_reg[i] ? downstream_x_resp_payload_reg[i].id : '0;

      br_mux_bin #(
          .NumSymbolsIn(NumIds),
          .SymbolWidth (SubIdWidth)
      ) br_mux_bin_ds_port_id (
          .select(mux_select),
          .in(resp_tracker_pop_sub_select_per_id),
          .out(next_port_for_id),
          .out_valid()
      );

      br_mux_bin #(
          .NumSymbolsIn(NumIds),
          .SymbolWidth (1)
      ) br_mux_bin_ds_port_id_valid (
          .select(mux_select),
          .in(resp_tracker_pop_valid_per_id),
          .out(next_port_for_id_valid),
          .out_valid()
      );
    end

    assign ds_port_id_match[i] = downstream_xvalid_reg[i]
                                    && next_port_for_id_valid
                                    && (next_port_for_id == i);
  end

  // A downstream port is eligible to be selected if:
  // 1. The response is valid.
  // 2. The downstream port is at the head of the tracking FIFO for the presented response ID.
  //
  // Additionally, if the upstream is not ready, we force all request inputs to 0, and force the
  // grant_hold input to the current grant. This is to prevent the grant/hold circuit (and attached
  // arbiter) from changing the grant when the upstream is not ready.
  assign ds_port_req = downstream_xvalid_reg
                        & ds_port_id_match
                        & {NumSubordinates{upstream_xready_pre}};

  // If upstream is ready, then grant hold is asserted unless a valid request is presented with
  // last=1. If upstream is not ready, then grant_hold is equal to the current grant (see above).
  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_ds_port_gnt_hold
    assign ds_port_gnt_hold[i] = upstream_xready_pre
                                    ? ~(ds_port_req[i] && downstream_x_resp_payload_reg[i].last)
                                    : ds_port_gnt[i];
  end

  // LRU arbiter w/ grant hold circuit
  logic [NumSubordinates-1:0] ds_port_gnt_from_arb;
  logic ds_port_gnt_enable_priority_update_to_arb;

  br_arb_grant_hold #(
      .NumRequesters(NumSubordinates)
  ) br_arb_grant_hold_ds_port (
      .clk,
      .rst,
      //
      .grant_hold(ds_port_gnt_hold),
      .enable_priority_update(1'b1),
      //
      .grant_from_arb(ds_port_gnt_from_arb),
      .enable_priority_update_to_arb(ds_port_gnt_enable_priority_update_to_arb),
      //
      .grant(ds_port_gnt)
  );

  br_arb_lru #(
      .NumRequesters(NumSubordinates)
  ) br_arb_lru_ds_port (
      .clk,
      .rst,
      //
      .request(ds_port_req),
      .grant(ds_port_gnt_from_arb),
      .enable_priority_update(ds_port_gnt_enable_priority_update_to_arb)
  );

  // Ready/valid joining
  assign downstream_xready_reg = ds_port_gnt & {NumSubordinates{upstream_xready_pre}};
  assign upstream_xvalid_pre = |(ds_port_req & ds_port_gnt);
  assign resp_tracker_pop_ready = upstream_x_resp_payload_pre.last
                                        && upstream_xvalid_pre
                                        && upstream_xready_pre;

  if (SingleIdOnly) begin : gen_single_id_only_enc
    assign resp_tracker_pop_ready_per_id = resp_tracker_pop_ready;
  end else begin : gen_multi_id_pop_ready_enc
    br_enc_bin2onehot #(
        .NumValues(NumIds)
    ) br_enc_bin2onehot_resp_tracker_pop (
        .clk,
        .rst,
        //
        .in(upstream_x_resp_payload_pre.id),
        .in_valid(resp_tracker_pop_ready),
        .out(resp_tracker_pop_ready_per_id)
    );
  end

  // Mux to select winning downstream port
  br_mux_onehot #(
      .NumSymbolsIn(NumSubordinates),
      .SymbolWidth (AxiIdWidth + RespPayloadWidth + 1)
  ) br_mux_onehot_downstream_resp (
      .select(ds_port_gnt),
      .in(downstream_x_resp_payload_reg),
      .out(upstream_x_resp_payload_pre)
  );

  // Output buffer (to cut upstream_xready -> upstream_xvalid path)
  br_flow_reg_fwd #(
      .Width(AxiIdWidth + RespPayloadWidth + 1),
      // If a higher-priority downstream port with a different ID becomes valid,
      // the mux select can change, resulting in data not remaining stable.
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_upstream_resp (
      .clk,
      .rst,
      //
      .push_ready(upstream_xready_pre),
      .push_valid(upstream_xvalid_pre),
      .push_data({
        upstream_x_resp_payload_pre.id,
        upstream_x_resp_payload_pre.payload,
        upstream_x_resp_payload_pre.last
      }),
      //
      .pop_ready(upstream_xready),
      .pop_valid(upstream_xvalid),
      .pop_data({upstream_xid, upstream_x_payload, upstream_xlast})
  );

  //
  // Implementation checks
  //

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_subordinate_checks
    br_flow_checks_valid_data_impl #(
        .NumFlows(1),
        .Width(AxiIdWidth + ReqPayloadWidth),
        .EnableCoverBackpressure(1),
        .EnableAssertValidStability(1),
        .EnableAssertDataStability(1),
        .EnableAssertFinalNotValid(1)
    ) br_flow_checks_valid_data_impl_downstream_resp (
        .clk,
        .rst,
        .ready(downstream_axready[i]),
        .valid(downstream_axvalid[i]),
        .data ({downstream_axid[i], downstream_ax_payload[i]})
    );
  end

  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(AxiIdWidth + RespPayloadWidth + 1),
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(1)
  ) br_flow_checks_valid_data_impl_upstream_req (
      .clk,
      .rst,
      //
      .ready(upstream_xready),
      .valid(upstream_xvalid),
      .data ({upstream_xid, upstream_x_payload, upstream_xlast})
  );
endmodule
