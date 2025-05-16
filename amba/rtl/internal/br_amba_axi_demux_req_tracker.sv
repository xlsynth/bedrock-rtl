`include "br_unused.svh"
`include "br_asserts_internal.svh"

module br_amba_axi_demux_req_tracker #(
    parameter int NumSubordinates = 2,
    parameter int AxiIdWidth = 1,
    parameter int MaxOutstanding = 3,
    parameter int ReqPayloadWidth = 1,
    parameter int RespPayloadWidth = 1,
    parameter int SingleIdOnly = 0,
    parameter int FifoStagingBufferDepth = 1,
    parameter int FifoNumLinkedListsPerFifo = 1,
    parameter int FifoRegisterPopOutputs = 1,
    parameter int FifoRegisterDeallocation = 1,
    parameter int FifoDataRamAddressDepthStages = 0,
    parameter int FifoDataRamReadDataDepthStages = 0,
    parameter int FifoPointerRamAddressDepthStages = 0,
    parameter int FifoPointerRamReadDataDepthStages = 0,
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

  //
  // Integration checks
  //

  `BR_ASSERT_STATIC(num_subordinates_gte_2_a, NumSubordinates >= 2)
  `BR_ASSERT_STATIC(max_outstanding_gte_1_a, MaxOutstanding >= 3)
  if (SingleIdOnly) begin : gen_single_id_only_checks
    `BR_ASSERT_INTG(axid_is_zero_a, upstream_axvalid |-> upstream_axid == '0)
    `BR_ASSERT_INTG(xid_is_zero_a, downstream_xvalid |-> downstream_xid == '0)
  end

  //
  // Internal signals
  //

  logic [SubIdWidth-1:0] upstream_ax_sub_select_int;
  logic [ReqPayloadWidth-1:0] upstream_ax_payload_int;
  logic [AxiIdWidth-1:0] upstream_axid_int;
  logic upstream_axready_int;
  logic upstream_axvalid_int;

  logic upstream_axready_reg;
  logic upstream_axvalid_reg;
  logic [AxiIdWidth-1:0] upstream_axid_reg;
  logic [SubIdWidth-1:0] upstream_ax_sub_select_reg;
  logic [ReqPayloadWidth-1:0] upstream_ax_payload_reg;

  logic resp_tracking_fifo_push_ready;
  logic resp_tracking_fifo_push_valid;
  logic [AxiIdWidth-1:0] resp_tracking_fifo_push_id;
  logic [SubIdWidth-1:0] resp_tracking_fifo_push_sub_select;

  logic [NumIds-1:0] resp_tracking_fifo_pop_ready_per_id;
  logic [NumIds-1:0] resp_tracking_fifo_pop_valid_per_id;
  logic [NumIds-1:0][SubIdWidth-1:0] resp_tracking_fifo_pop_sub_select_per_id;
  logic resp_tracking_fifo_pop_ready;

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
      .pop_ready({wdata_flow_ready, resp_tracking_fifo_push_ready, upstream_axready_int}),
      .pop_valid_unstable({wdata_flow_valid, resp_tracking_fifo_push_valid, upstream_axvalid_int})
  );

  assign upstream_ax_payload_int = upstream_ax_payload_reg;
  assign upstream_ax_sub_select_int = upstream_ax_sub_select_reg;
  assign upstream_axid_int = upstream_axid_reg;

  assign wdata_flow_sub_select = upstream_ax_sub_select_reg;

  assign resp_tracking_fifo_push_id = upstream_axid_reg;
  assign resp_tracking_fifo_push_sub_select = upstream_ax_sub_select_reg;

  // Request tracking FIFO
  if (SingleIdOnly) begin : gen_single_id_only_fifo
    `BR_UNUSED(resp_tracking_fifo_push_id)

    br_fifo_flops #(
        .Depth(MaxOutstanding),
        .Width(SubIdWidth),
        // When downstream backpressures, push_valid can drop.
        .EnableAssertPushValidStability(0)
    ) br_fifo_flops_resp_tracking (
        .clk,
        .rst,
        //
        .push_ready(resp_tracking_fifo_push_ready),
        .push_valid(resp_tracking_fifo_push_valid),
        .push_data(resp_tracking_fifo_push_sub_select),
        //
        .pop_ready(resp_tracking_fifo_pop_ready_per_id),
        .pop_valid(resp_tracking_fifo_pop_valid_per_id),
        .pop_data(resp_tracking_fifo_pop_sub_select_per_id),
        //
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        //
        .empty(),
        .empty_next(),
        .items(),
        .items_next()
    );
  end else begin : gen_multi_id_fifo
    br_fifo_shared_dynamic_flops #(
        .NumFifos(NumIds),
        .Depth(MaxOutstanding),
        .Width(SubIdWidth),
        .StagingBufferDepth(FifoStagingBufferDepth),
        .NumLinkedListsPerFifo(FifoNumLinkedListsPerFifo),
        .RegisterPopOutputs(FifoRegisterPopOutputs),
        .RegisterDeallocation(FifoRegisterDeallocation),
        .DataRamDepthTiles(1),
        .DataRamAddressDepthStages(FifoDataRamAddressDepthStages),
        .DataRamReadDataDepthStages(FifoDataRamReadDataDepthStages),
        .DataRamReadDataWidthStages(1),
        .PointerRamDepthTiles(1),
        .PointerRamAddressDepthStages(FifoPointerRamAddressDepthStages),
        .PointerRamReadDataDepthStages(FifoPointerRamReadDataDepthStages),
        .PointerRamReadDataWidthStages(1),
        // When downstream backpressures, push_valid can drop.
        .EnableAssertPushValidStability(0)
    ) br_fifo_shared_dynamic_flops_resp_tracking (
        .clk,
        .rst,
        //
        .push_valid(resp_tracking_fifo_push_valid),
        .push_ready(resp_tracking_fifo_push_ready),
        .push_data(resp_tracking_fifo_push_sub_select),
        .push_fifo_id(resp_tracking_fifo_push_id),
        .push_full(),
        //
        .pop_valid(resp_tracking_fifo_pop_valid_per_id),
        .pop_ready(resp_tracking_fifo_pop_ready_per_id),
        .pop_data(resp_tracking_fifo_pop_sub_select_per_id),
        .pop_empty()
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
      .push_data({upstream_axid_int, upstream_ax_payload_int}),
      //
      .pop_ready(downstream_axready),
      .pop_valid_unstable(downstream_axvalid),
      .pop_data_unstable({downstream_axid, downstream_ax_payload})
  );

  //
  // Response Path
  //

  logic [NumSubordinates-1:0] downstream_xready_reg;
  logic [NumSubordinates-1:0] downstream_xvalid_reg;
  logic [NumSubordinates-1:0][AxiIdWidth-1:0] downstream_xid_reg;
  logic [NumSubordinates-1:0][RespPayloadWidth-1:0] downstream_x_payload_reg;
  logic [NumSubordinates-1:0] downstream_xlast_reg;

  logic upstream_xready_reg;
  logic upstream_xvalid_reg;
  logic [AxiIdWidth-1:0] upstream_xid_reg;
  logic [RespPayloadWidth-1:0] upstream_x_payload_reg;
  logic upstream_xlast_reg;

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
        .push_data ({downstream_xid[i], downstream_x_payload[i], downstream_xlast[i]}),
        //
        .pop_ready (downstream_xready_reg[i]),
        .pop_valid (downstream_xvalid_reg[i]),
        .pop_data  ({downstream_xid_reg[i], downstream_x_payload_reg[i], downstream_xlast_reg[i]})
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
      assign next_port_for_id = resp_tracking_fifo_pop_sub_select_per_id;
      assign next_port_for_id_valid = resp_tracking_fifo_pop_valid_per_id;
    end else begin : gen_multi_id_pop_mux
      logic [AxiIdWidth-1:0] mux_select;
      assign mux_select = downstream_xvalid_reg[i] ? downstream_xid_reg[i] : '0;

      br_mux_bin #(
          .NumSymbolsIn(NumIds),
          .SymbolWidth (SubIdWidth)
      ) br_mux_bin_ds_port_id (
          .select(mux_select),
          .in(resp_tracking_fifo_pop_sub_select_per_id),
          .out(next_port_for_id),
          .out_valid()
      );

      br_mux_bin #(
          .NumSymbolsIn(NumIds),
          .SymbolWidth (1)
      ) br_mux_bin_ds_port_id_valid (
          .select(mux_select),
          .in(resp_tracking_fifo_pop_valid_per_id),
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
  assign ds_port_req = downstream_xvalid_reg & ds_port_id_match;
  assign ds_port_gnt_hold = ~downstream_xlast_reg;

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
  assign downstream_xready_reg = ds_port_gnt & {NumSubordinates{upstream_xready_reg}};
  assign upstream_xvalid_reg = |ds_port_req;
  assign resp_tracking_fifo_pop_ready = upstream_xlast_reg
                                        && upstream_xvalid_reg
                                        && upstream_xready_reg;

  if (SingleIdOnly) begin : gen_single_id_only_enc
    assign resp_tracking_fifo_pop_ready_per_id = resp_tracking_fifo_pop_ready;
  end else begin : gen_multi_id_pop_ready_enc
    br_enc_bin2onehot #(
        .NumValues(NumIds)
    ) br_enc_bin2onehot_resp_tracking_fifo_pop (
        .clk,
        .rst,
        //
        .in(upstream_xid_reg),
        .in_valid(resp_tracking_fifo_pop_ready),
        .out(resp_tracking_fifo_pop_ready_per_id)
    );
  end

  // Mux to select winning downstream port
  br_mux_onehot #(
      .NumSymbolsIn(NumSubordinates),
      .SymbolWidth (AxiIdWidth + RespPayloadWidth + 1)
  ) br_mux_onehot_downstream_resp (
      .select(ds_port_gnt),
      .in({downstream_xid_reg, downstream_x_payload_reg, downstream_xlast_reg}),
      .out({upstream_xid_reg, upstream_x_payload_reg, upstream_xlast_reg})
  );

  // Output buffer (to cut upstream_xready -> upstream_xvalid path)
  br_flow_reg_fwd #(
      .Width(AxiIdWidth + RespPayloadWidth + 1)
  ) br_flow_reg_fwd_upstream_resp (
      .clk,
      .rst,
      //
      .push_ready(upstream_xready_reg),
      .push_valid(upstream_xvalid_reg),
      .push_data ({upstream_xid_reg, upstream_x_payload_reg, upstream_xlast_reg}),
      //
      .pop_ready (upstream_xready),
      .pop_valid (upstream_xvalid),
      .pop_data  ({upstream_xid, upstream_x_payload, upstream_xlast})
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
