// SPDX-License-Identifier: Apache-2.0

module br_amba_axi_demux #(
    // Number of downstream subordinates.
    parameter int NumSubordinates = 2,
    // Width of the AXI ID field for the write path.
    parameter int AwAxiIdWidth = 1,
    // Width of the AXI ID field for the read path.
    parameter int ArAxiIdWidth = 1,
    // Maximum number of outstanding write transactions per ID.
    parameter int AwMaxOutstandingPerId = 3,
    // Maximum number of outstanding read transactions per ID.
    parameter int ArMaxOutstandingPerId = 3,
    // If 1, then only a single ID is supported on both the write and read paths.
    parameter int SingleIdOnly = 0,
    // Depth of the write data buffer. This number of WDATA pushes can be buffered
    // before the write address is accepted.
    parameter int WdataBufferDepth = 2,
    // Maximum number of outstanding write transactions that can be accepted before
    // corresponding WDATA pushes are accepted.
    parameter int MaxAwRunahead = 4,
    // If 1, then downstream AW/AR outputs are registered.
    parameter int RegisterDownstreamAxOutputs = 1,
    // If 1, then downstream WDATA outputs are registered.
    parameter int RegisterDownstreamWOutputs = 1,
    // Width of the AXI address field.
    parameter int AddrWidth = 12,
    // Width of the AXI data field.
    parameter int DataWidth = 32,
    // Width of the AXI AWUSER field.
    parameter int AWUserWidth = 1,
    // Width of the AXI WUSER field.
    parameter int WUserWidth = 1,
    // Width of the AXI ARUSER field.
    parameter int ARUserWidth = 1,
    // Width of the AXI BUSER field.
    parameter int BUserWidth = 1,
    // Width of the AXI RUSER field.
    parameter int RUserWidth = 1,
    //
    localparam int StrobeWidth = DataWidth / 8,
    localparam int SubIdWidth = $clog2(NumSubordinates)
) (
    input logic clk,
    input logic rst,
    //
    input logic [SubIdWidth-1:0] upstream_aw_sub_select,
    //
    input logic [AddrWidth-1:0] upstream_awaddr,
    input logic [AwAxiIdWidth-1:0] upstream_awid,
    input logic [br_amba::AxiBurstLenWidth-1:0] upstream_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_awburst,
    input logic [br_amba::AxiCacheWidth-1:0] upstream_awcache,
    input logic [br_amba::AxiProtWidth-1:0] upstream_awprot,
    input logic [AWUserWidth-1:0] upstream_awuser,
    input logic upstream_awvalid,
    output logic upstream_awready,
    input logic [DataWidth-1:0] upstream_wdata,
    input logic [StrobeWidth-1:0] upstream_wstrb,
    input logic [WUserWidth-1:0] upstream_wuser,
    input logic upstream_wlast,
    input logic upstream_wvalid,
    output logic upstream_wready,
    output logic [AwAxiIdWidth-1:0] upstream_bid,
    output logic [BUserWidth-1:0] upstream_buser,
    output logic [br_amba::AxiRespWidth-1:0] upstream_bresp,
    output logic upstream_bvalid,
    input logic upstream_bready,
    //
    input logic [SubIdWidth-1:0] upstream_ar_sub_select,
    //
    input logic [AddrWidth-1:0] upstream_araddr,
    input logic [ArAxiIdWidth-1:0] upstream_arid,
    input logic [br_amba::AxiBurstLenWidth-1:0] upstream_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_arburst,
    input logic [br_amba::AxiCacheWidth-1:0] upstream_arcache,
    input logic [br_amba::AxiProtWidth-1:0] upstream_arprot,
    input logic [ARUserWidth-1:0] upstream_aruser,
    input logic upstream_arvalid,
    output logic upstream_arready,
    output logic [ArAxiIdWidth-1:0] upstream_rid,
    output logic [DataWidth-1:0] upstream_rdata,
    output logic [RUserWidth-1:0] upstream_ruser,
    output logic [br_amba::AxiRespWidth-1:0] upstream_rresp,
    output logic upstream_rlast,
    output logic upstream_rvalid,
    input logic upstream_rready,
    //
    output logic [NumSubordinates-1:0][AddrWidth-1:0] downstream_awaddr,
    output logic [NumSubordinates-1:0][AwAxiIdWidth-1:0] downstream_awid,
    output logic [NumSubordinates-1:0][br_amba::AxiBurstLenWidth-1:0] downstream_awlen,
    output logic [NumSubordinates-1:0][br_amba::AxiBurstSizeWidth-1:0] downstream_awsize,
    output logic [NumSubordinates-1:0][br_amba::AxiBurstTypeWidth-1:0] downstream_awburst,
    output logic [NumSubordinates-1:0][br_amba::AxiCacheWidth-1:0] downstream_awcache,
    output logic [NumSubordinates-1:0][br_amba::AxiProtWidth-1:0] downstream_awprot,
    output logic [NumSubordinates-1:0][AWUserWidth-1:0] downstream_awuser,
    output logic [NumSubordinates-1:0] downstream_awvalid,
    input logic [NumSubordinates-1:0] downstream_awready,
    output logic [NumSubordinates-1:0][DataWidth-1:0] downstream_wdata,
    output logic [NumSubordinates-1:0][StrobeWidth-1:0] downstream_wstrb,
    output logic [NumSubordinates-1:0][WUserWidth-1:0] downstream_wuser,
    output logic [NumSubordinates-1:0] downstream_wlast,
    output logic [NumSubordinates-1:0] downstream_wvalid,
    input logic [NumSubordinates-1:0] downstream_wready,
    input logic [NumSubordinates-1:0][AwAxiIdWidth-1:0] downstream_bid,
    input logic [NumSubordinates-1:0][BUserWidth-1:0] downstream_buser,
    input logic [NumSubordinates-1:0][br_amba::AxiRespWidth-1:0] downstream_bresp,
    input logic [NumSubordinates-1:0] downstream_bvalid,
    output logic [NumSubordinates-1:0] downstream_bready,
    output logic [NumSubordinates-1:0][AddrWidth-1:0] downstream_araddr,
    output logic [NumSubordinates-1:0][ArAxiIdWidth-1:0] downstream_arid,
    output logic [NumSubordinates-1:0][br_amba::AxiBurstLenWidth-1:0] downstream_arlen,
    output logic [NumSubordinates-1:0][br_amba::AxiBurstSizeWidth-1:0] downstream_arsize,
    output logic [NumSubordinates-1:0][br_amba::AxiBurstTypeWidth-1:0] downstream_arburst,
    output logic [NumSubordinates-1:0][br_amba::AxiCacheWidth-1:0] downstream_arcache,
    output logic [NumSubordinates-1:0][br_amba::AxiProtWidth-1:0] downstream_arprot,
    output logic [NumSubordinates-1:0][ARUserWidth-1:0] downstream_aruser,
    output logic [NumSubordinates-1:0] downstream_arvalid,
    input logic [NumSubordinates-1:0] downstream_arready,
    input logic [NumSubordinates-1:0][ArAxiIdWidth-1:0] downstream_rid,
    input logic [NumSubordinates-1:0][DataWidth-1:0] downstream_rdata,
    input logic [NumSubordinates-1:0][RUserWidth-1:0] downstream_ruser,
    input logic [NumSubordinates-1:0][br_amba::AxiRespWidth-1:0] downstream_rresp,
    input logic [NumSubordinates-1:0] downstream_rlast,
    input logic [NumSubordinates-1:0] downstream_rvalid,
    output logic [NumSubordinates-1:0] downstream_rready
);

  typedef struct packed {
    logic [AddrWidth-1:0] addr;
    logic [br_amba::AxiBurstLenWidth-1:0] len;
    logic [br_amba::AxiBurstSizeWidth-1:0] size;
    logic [br_amba::AxiBurstTypeWidth-1:0] burst;
    logic [br_amba::AxiCacheWidth-1:0] cache;
    logic [br_amba::AxiProtWidth-1:0] prot;
    logic [ARUserWidth-1:0] user;
  } ar_req_t;

  typedef struct packed {
    logic [AddrWidth-1:0] addr;
    logic [br_amba::AxiBurstLenWidth-1:0] len;
    logic [br_amba::AxiBurstSizeWidth-1:0] size;
    logic [br_amba::AxiBurstTypeWidth-1:0] burst;
    logic [br_amba::AxiCacheWidth-1:0] cache;
    logic [br_amba::AxiProtWidth-1:0] prot;
    logic [AWUserWidth-1:0] user;
  } aw_req_t;

  ar_req_t upstream_ar_req;
  ar_req_t [NumSubordinates-1:0] downstream_ar_req;
  aw_req_t upstream_aw_req;
  aw_req_t [NumSubordinates-1:0] downstream_aw_req;

  //
  // Read Path
  //
  assign upstream_ar_req = '{
          addr: upstream_araddr,
          len: upstream_arlen,
          size: upstream_arsize,
          burst: upstream_arburst,
          cache: upstream_arcache,
          prot: upstream_arprot,
          user: upstream_aruser
      };

  typedef struct packed {
    logic [RUserWidth-1:0] user;
    logic [DataWidth-1:0] data;
    logic [br_amba::AxiRespWidth-1:0] resp;
  } rdata_bundle_t;

  rdata_bundle_t upstream_rdata_bundle;
  rdata_bundle_t [NumSubordinates-1:0] downstream_rdata_bundle;

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_rdata_bundle
    assign downstream_rdata_bundle[i] = '{
            user: downstream_ruser[i],
            data: downstream_rdata[i],
            resp: downstream_rresp[i]
        };
  end

  assign upstream_rdata = upstream_rdata_bundle.data;
  assign upstream_ruser = upstream_rdata_bundle.user;
  assign upstream_rresp = upstream_rdata_bundle.resp;

  br_amba_axi_demux_req_tracker #(
      .NumSubordinates(NumSubordinates),
      .AxiIdWidth(ArAxiIdWidth),
      .MaxOutstandingPerId(ArMaxOutstandingPerId),
      .ReqPayloadWidth(AddrWidth
                        + br_amba::AxiBurstLenWidth
                        + br_amba::AxiBurstSizeWidth
                        + br_amba::AxiBurstTypeWidth
                        + br_amba::AxiCacheWidth
                        + br_amba::AxiProtWidth
                        + ARUserWidth),
      .RespPayloadWidth(DataWidth + RUserWidth + br_amba::AxiRespWidth),
      .SingleIdOnly(SingleIdOnly),
      .RegisterDownstreamOutputs(RegisterDownstreamAxOutputs)
  ) br_amba_axi_demux_req_tracker_ar (
      .clk,
      .rst,
      //
      .upstream_axready(upstream_arready),
      .upstream_axvalid(upstream_arvalid),
      .upstream_axid(upstream_arid),
      .upstream_ax_sub_select(upstream_ar_sub_select),
      .upstream_ax_payload(upstream_ar_req),
      //
      .downstream_axready(downstream_arready),
      .downstream_axvalid(downstream_arvalid),
      .downstream_axid(downstream_arid),
      .downstream_ax_payload(downstream_ar_req),
      //
      .upstream_xready(upstream_rready),
      .upstream_xvalid(upstream_rvalid),
      .upstream_xid(upstream_rid),
      .upstream_xlast(upstream_rlast),
      .upstream_x_payload(upstream_rdata_bundle),
      //
      .downstream_xready(downstream_rready),
      .downstream_xvalid(downstream_rvalid),
      .downstream_xid(downstream_rid),
      .downstream_xlast(downstream_rlast),
      .downstream_x_payload(downstream_rdata_bundle),
      //
      .wdata_flow_ready(1'b1),
      .wdata_flow_valid(),
      .wdata_flow_sub_select()
  );

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_ar_unpack
    assign downstream_araddr[i]  = downstream_ar_req[i].addr;
    assign downstream_arlen[i]   = downstream_ar_req[i].len;
    assign downstream_arsize[i]  = downstream_ar_req[i].size;
    assign downstream_arburst[i] = downstream_ar_req[i].burst;
    assign downstream_arcache[i] = downstream_ar_req[i].cache;
    assign downstream_arprot[i]  = downstream_ar_req[i].prot;
    assign downstream_aruser[i]  = downstream_ar_req[i].user;
  end

  //
  // Write Path
  //
  assign upstream_aw_req = '{
          addr: upstream_awaddr,
          len: upstream_awlen,
          size: upstream_awsize,
          burst: upstream_awburst,
          cache: upstream_awcache,
          prot: upstream_awprot,
          user: upstream_awuser
      };

  typedef struct packed {
    logic [WUserWidth-1:0] user;
    logic [DataWidth-1:0] data;
    logic [StrobeWidth-1:0] strb;
    logic last;
  } wdata_req_t;

  typedef struct packed {
    logic [BUserWidth-1:0] user;
    logic [br_amba::AxiRespWidth-1:0] resp;
  } bresp_bundle_t;

  bresp_bundle_t upstream_bresp_bundle;
  bresp_bundle_t [NumSubordinates-1:0] downstream_bresp_bundle;

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_bresp_bundle
    assign downstream_bresp_bundle[i] = '{user: downstream_buser[i], resp: downstream_bresp[i]};
  end

  assign upstream_bresp = upstream_bresp_bundle.resp;
  assign upstream_buser = upstream_bresp_bundle.user;

  logic wdata_flow_ready;
  logic wdata_flow_valid;
  logic [SubIdWidth-1:0] wdata_flow_sub_select;

  logic wdata_flow_valid_buf;
  logic wdata_flow_ready_buf;
  logic [SubIdWidth-1:0] wdata_flow_sub_select_buf;

  logic upstream_wvalid_buf;
  logic upstream_wready_buf;
  wdata_req_t upstream_wdata_req_buf;

  logic downstream_wvalid_int;
  logic downstream_wready_int;

  br_amba_axi_demux_req_tracker #(
      .NumSubordinates(NumSubordinates),
      .AxiIdWidth(AwAxiIdWidth),
      .MaxOutstandingPerId(AwMaxOutstandingPerId),
      .ReqPayloadWidth(AddrWidth
                        + br_amba::AxiBurstLenWidth
                        + br_amba::AxiBurstSizeWidth
                        + br_amba::AxiBurstTypeWidth
                        + br_amba::AxiCacheWidth
                        + br_amba::AxiProtWidth
                        + AWUserWidth),
      .RespPayloadWidth(BUserWidth + br_amba::AxiRespWidth),
      .SingleIdOnly(SingleIdOnly),
      .RegisterDownstreamOutputs(RegisterDownstreamAxOutputs)
  ) br_amba_axi_demux_req_tracker_aw (
      .clk,
      .rst,
      //
      .upstream_axready(upstream_awready),
      .upstream_axvalid(upstream_awvalid),
      .upstream_axid(upstream_awid),
      .upstream_ax_sub_select(upstream_aw_sub_select),
      .upstream_ax_payload(upstream_aw_req),
      //
      .downstream_axready(downstream_awready),
      .downstream_axvalid(downstream_awvalid),
      .downstream_axid(downstream_awid),
      .downstream_ax_payload(downstream_aw_req),
      //
      .upstream_xready(upstream_bready),
      .upstream_xvalid(upstream_bvalid),
      .upstream_xid(upstream_bid),
      .upstream_xlast(),
      .upstream_x_payload(upstream_bresp_bundle),
      //
      .downstream_xready(downstream_bready),
      .downstream_xvalid(downstream_bvalid),
      .downstream_xid(downstream_bid),
      .downstream_xlast({NumSubordinates{1'b1}}),
      .downstream_x_payload(downstream_bresp_bundle),
      //
      .wdata_flow_ready(wdata_flow_ready),
      .wdata_flow_valid(wdata_flow_valid),
      .wdata_flow_sub_select(wdata_flow_sub_select)
  );

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_aw_unpack
    assign downstream_awaddr[i]  = downstream_aw_req[i].addr;
    assign downstream_awlen[i]   = downstream_aw_req[i].len;
    assign downstream_awsize[i]  = downstream_aw_req[i].size;
    assign downstream_awburst[i] = downstream_aw_req[i].burst;
    assign downstream_awcache[i] = downstream_aw_req[i].cache;
    assign downstream_awprot[i]  = downstream_aw_req[i].prot;
    assign downstream_awuser[i]  = downstream_aw_req[i].user;
  end

  br_fifo_flops #(
      .Depth(WdataBufferDepth),
      .Width(DataWidth + WUserWidth + StrobeWidth + 1)
  ) br_fifo_flops_wdata_buffer (
      .clk,
      .rst,
      //
      .push_valid(upstream_wvalid),
      .push_ready(upstream_wready),
      .push_data({upstream_wuser, upstream_wdata, upstream_wstrb, upstream_wlast}),
      //
      .pop_valid(upstream_wvalid_buf),
      .pop_ready(upstream_wready_buf),
      .pop_data({
        upstream_wdata_req_buf.user,
        upstream_wdata_req_buf.data,
        upstream_wdata_req_buf.strb,
        upstream_wdata_req_buf.last
      }),
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

  br_fifo_flops #(
      .Depth(MaxAwRunahead),
      .Width(SubIdWidth),
      // Valid can drop if downstream deasserts ready.
      .EnableAssertPushValidStability(0)
  ) br_fifo_flops_wdata_flow_buffer (
      .clk,
      .rst,
      //
      .push_valid(wdata_flow_valid),
      .push_ready(wdata_flow_ready),
      .push_data(wdata_flow_sub_select),
      //
      .pop_valid(wdata_flow_valid_buf),
      .pop_ready(wdata_flow_ready_buf),
      .pop_data(wdata_flow_sub_select_buf),
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

  assign downstream_wvalid_int = upstream_wvalid_buf && wdata_flow_valid_buf;
  assign upstream_wready_buf = downstream_wready_int && wdata_flow_valid_buf;
  assign wdata_flow_ready_buf  = downstream_wready_int
                                && upstream_wvalid_buf
                                && upstream_wdata_req_buf.last;

  logic [SubIdWidth-1:0] downstream_w_sub_select;
  assign downstream_w_sub_select = wdata_flow_valid_buf ? wdata_flow_sub_select_buf : '0;

  wdata_req_t [NumSubordinates-1:0] downstream_wdata_req_pre;
  logic [NumSubordinates-1:0] downstream_wready_pre;
  logic [NumSubordinates-1:0] downstream_wvalid_pre;

  br_flow_demux_select_unstable #(
      .NumFlows(NumSubordinates),
      .Width(DataWidth + WUserWidth + StrobeWidth + 1)
  ) br_flow_demux_select_unstable_downstream_wdata (
      .clk,
      .rst,
      //
      .select(downstream_w_sub_select),
      //
      .push_ready(downstream_wready_int),
      .push_valid(downstream_wvalid_int),
      .push_data(upstream_wdata_req_buf),
      //
      .pop_ready(downstream_wready_pre),
      .pop_valid_unstable(downstream_wvalid_pre),
      .pop_data_unstable(downstream_wdata_req_pre)
  );

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_wdata_unpack
    if (RegisterDownstreamWOutputs) begin : gen_register_downstream_wdata_outputs
      br_flow_reg_fwd #(
          .Width(DataWidth + WUserWidth + StrobeWidth + 1)
      ) br_flow_reg_fwd_downstream_wdata (
          .clk,
          .rst,
          //
          .push_ready(downstream_wready_pre[i]),
          .push_valid(downstream_wvalid_pre[i]),
          .push_data({
            downstream_wdata_req_pre[i].user,
            downstream_wdata_req_pre[i].data,
            downstream_wdata_req_pre[i].strb,
            downstream_wdata_req_pre[i].last
          }),
          //
          .pop_ready(downstream_wready[i]),
          .pop_valid(downstream_wvalid[i]),
          .pop_data({
            downstream_wuser[i], downstream_wdata[i], downstream_wstrb[i], downstream_wlast[i]
          })
      );
    end else begin : gen_no_register_downstream_wdata_outputs
      assign downstream_wready_pre[i] = downstream_wready[i];
      assign downstream_wvalid[i] = downstream_wvalid_pre[i];
      assign downstream_wuser[i] = downstream_wdata_req_pre[i].user;
      assign downstream_wdata[i] = downstream_wdata_req_pre[i].data;
      assign downstream_wstrb[i] = downstream_wdata_req_pre[i].strb;
      assign downstream_wlast[i] = downstream_wdata_req_pre[i].last;
    end


  end

  //
  // Implementation Checks
  //

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_downstream_wdata_checks
    br_flow_checks_valid_data_impl #(
        .NumFlows(1),
        .Width(DataWidth + WUserWidth + StrobeWidth + 1),
        .EnableCoverBackpressure(1),
        .EnableAssertValidStability(1),
        .EnableAssertDataStability(1),
        .EnableAssertFinalNotValid(1)
    ) br_flow_checks_valid_data_impl_downstream_wdata (
        .clk,
        .rst,
        //
        .ready(downstream_wready[i]),
        .valid(downstream_wvalid[i]),
        .data ({downstream_wuser[i], downstream_wdata[i], downstream_wstrb[i], downstream_wlast[i]})
    );
  end

endmodule
