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
// Bedrock-RTL AXI Demux
//
// Allows a single AXI Manager to drive multiple AXI Subordinates. The
// upstream_ax_sub_select signal is used to select which subordinate to route
// the request to.
//
// Read response data interleaving is not supported.

module br_amba_axi_demux #(
    // Number of downstream subordinates.
    parameter int NumSubordinates = 2,
    // Width of the AXI ID field for the write path.
    parameter int AwAxiIdWidth = 1,
    // Width of the AXI ID field for the read path.
    parameter int ArAxiIdWidth = 1,
    // Maximum number of outstanding write transactions.
    parameter int AwMaxOutstanding = 3,
    // Maximum number of outstanding read transactions.
    parameter int ArMaxOutstanding = 3,
    // If 1, then only a single ID is supported on both the write and read paths.
    parameter int SingleIdOnly = 0,
    // Depth of the write data buffer. This number of WDATA pushes can be buffered
    // before the write address is accepted.
    parameter int WdataBufferDepth = 2,
    // Maximum number of outstanding write transactions that can be accepted before
    // corresponding WDATA pushes are accepted.
    parameter int MaxAwRunahead = 4,
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
    // Number of pipeline stages to use for the pointer RAM read
    // data in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoPointerRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the data RAM read data
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoDataRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the pointer RAM address
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoPointerRamAddressDepthStages = 1,
    // Number of pipeline stages to use for the data RAM address
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoDataRamAddressDepthStages = 1,
    // Number of linked lists per FIFO in the response tracker FIFO. Has
    // no effect if SingleIdOnly == 1.
    parameter int FifoNumLinkedListsPerFifo = 2,
    // Number of pipeline stages to use for the staging buffer
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoStagingBufferDepth = 2,
    // Number of pipeline stages to use for the pop outputs
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoRegisterPopOutputs = 1,
    // Number of pipeline stages to use for the deallocation
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoRegisterDeallocation = 1,
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

  //
  // Read Path
  //

  br_amba_axi_demux_req_tracker #(
      .NumSubordinates(NumSubordinates),
      .AxiIdWidth(ArAxiIdWidth),
      .MaxOutstanding(ArMaxOutstanding),
      .ReqPayloadWidth(AddrWidth
                        + br_amba::AxiBurstLenWidth
                        + br_amba::AxiBurstSizeWidth
                        + br_amba::AxiBurstTypeWidth
                        + br_amba::AxiCacheWidth
                        + br_amba::AxiProtWidth
                        + ARUserWidth),
      .RespPayloadWidth(DataWidth + RUserWidth + br_amba::AxiRespWidth),
      .SingleIdOnly(SingleIdOnly),
      .FifoPointerRamReadDataDepthStages(FifoPointerRamReadDataDepthStages),
      .FifoDataRamReadDataDepthStages(FifoDataRamReadDataDepthStages),
      .FifoPointerRamAddressDepthStages(FifoPointerRamAddressDepthStages),
      .FifoDataRamAddressDepthStages(FifoDataRamAddressDepthStages),
      .FifoNumLinkedListsPerFifo(FifoNumLinkedListsPerFifo),
      .FifoStagingBufferDepth(FifoStagingBufferDepth),
      .FifoRegisterPopOutputs(FifoRegisterPopOutputs),
      .FifoRegisterDeallocation(FifoRegisterDeallocation)
  ) br_amba_axi_demux_req_tracker (
      .clk,
      .rst,
      //
      .upstream_axready(upstream_arready),
      .upstream_axvalid(upstream_arvalid),
      .upstream_axid(upstream_arid),
      .upstream_ax_sub_select(upstream_ar_sub_select),
      .upstream_ax_payload({
        upstream_araddr,
        upstream_arlen,
        upstream_arsize,
        upstream_arburst,
        upstream_arcache,
        upstream_arprot,
        upstream_aruser
      }),
      //
      .downstream_axready(downstream_arready),
      .downstream_axvalid(downstream_arvalid),
      .downstream_axid(downstream_arid),
      .downstream_ax_payload({
        downstream_araddr,
        downstream_arlen,
        downstream_arsize,
        downstream_arburst,
        downstream_arcache,
        downstream_arprot,
        downstream_aruser
      }),
      //
      .upstream_xready(upstream_rready),
      .upstream_xvalid(upstream_rvalid),
      .upstream_xid(upstream_rid),
      .upstream_xlast(upstream_rlast),
      .upstream_x_payload({upstream_rdata, upstream_ruser, upstream_rresp}),
      //
      .downstream_xready(downstream_rready),
      .downstream_xvalid(downstream_rvalid),
      .downstream_xid(downstream_rid),
      .downstream_xlast(downstream_rlast),
      .downstream_x_payload({downstream_rdata, downstream_ruser, downstream_rresp}),
      //
      .wdata_flow_ready(1'b1),
      .wdata_flow_valid(),
      .wdata_flow_sub_select()
  );

  //
  // Write Path
  //

  logic wdata_flow_ready;
  logic wdata_flow_valid;
  logic [SubIdWidth-1:0] wdata_flow_sub_select;

  logic wdata_flow_valid_buf;
  logic wdata_flow_ready_buf;
  logic [SubIdWidth-1:0] wdata_flow_sub_select_buf;

  logic upstream_wvalid_buf;
  logic upstream_wready_buf;
  logic upstream_wlast_buf;
  logic [DataWidth-1:0] upstream_wdata_buf;
  logic [StrobeWidth-1:0] upstream_wstrb_buf;
  logic [WUserWidth-1:0] upstream_wuser_buf;

  logic downstream_wvalid_int;
  logic downstream_wready_int;

  br_amba_axi_demux_req_tracker #(
      .NumSubordinates(NumSubordinates),
      .AxiIdWidth(AwAxiIdWidth),
      .MaxOutstanding(AwMaxOutstanding),
      .ReqPayloadWidth(AddrWidth
                        + br_amba::AxiBurstLenWidth
                        + br_amba::AxiBurstSizeWidth
                        + br_amba::AxiBurstTypeWidth
                        + br_amba::AxiCacheWidth
                        + br_amba::AxiProtWidth
                        + AWUserWidth),
      .RespPayloadWidth(BUserWidth + br_amba::AxiRespWidth),
      .SingleIdOnly(SingleIdOnly),
      .FifoPointerRamReadDataDepthStages(FifoPointerRamReadDataDepthStages),
      .FifoDataRamReadDataDepthStages(FifoDataRamReadDataDepthStages),
      .FifoPointerRamAddressDepthStages(FifoPointerRamAddressDepthStages),
      .FifoDataRamAddressDepthStages(FifoDataRamAddressDepthStages),
      .FifoNumLinkedListsPerFifo(FifoNumLinkedListsPerFifo),
      .FifoStagingBufferDepth(FifoStagingBufferDepth),
      .FifoRegisterPopOutputs(FifoRegisterPopOutputs),
      .FifoRegisterDeallocation(FifoRegisterDeallocation)
  ) br_amba_axi_demux_req_tracker_aw (
      .clk,
      .rst,
      //
      .upstream_axready(upstream_awready),
      .upstream_axvalid(upstream_awvalid),
      .upstream_axid(upstream_awid),
      .upstream_ax_sub_select(upstream_aw_sub_select),
      .upstream_ax_payload({
        upstream_awaddr,
        upstream_awlen,
        upstream_awsize,
        upstream_awburst,
        upstream_awcache,
        upstream_awprot,
        upstream_awuser
      }),
      //
      .downstream_axready(downstream_awready),
      .downstream_axvalid(downstream_awvalid),
      .downstream_axid(downstream_awid),
      .downstream_ax_payload({
        downstream_awaddr,
        downstream_awlen,
        downstream_awsize,
        downstream_awburst,
        downstream_awcache,
        downstream_awprot,
        downstream_awuser
      }),
      //
      .upstream_xready(upstream_bready),
      .upstream_xvalid(upstream_bvalid),
      .upstream_xid(upstream_bid),
      .upstream_xlast(),
      .upstream_x_payload({upstream_buser, upstream_bresp}),
      //
      .downstream_xready(downstream_bready),
      .downstream_xvalid(downstream_bvalid),
      .downstream_xid(downstream_bid),
      .downstream_xlast({NumSubordinates{1'b1}}),
      .downstream_x_payload({downstream_buser, downstream_bresp}),
      //
      .wdata_flow_ready(wdata_flow_ready),
      .wdata_flow_valid(wdata_flow_valid),
      .wdata_flow_sub_select(wdata_flow_sub_select)
  );

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
      .pop_data({upstream_wuser_buf, upstream_wdata_buf, upstream_wstrb_buf, upstream_wlast_buf}),
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
      .Width(SubIdWidth)
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
  assign upstream_wready_buf   = downstream_wready_int && wdata_flow_valid_buf;
  assign wdata_flow_ready_buf  = downstream_wready_int && upstream_wvalid_buf && upstream_wlast_buf;

  logic [SubIdWidth-1:0] downstream_w_sub_select;
  assign downstream_w_sub_select = wdata_flow_valid_buf ? wdata_flow_sub_select_buf : '0;

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
      .push_data({upstream_wuser_buf, upstream_wdata_buf, upstream_wstrb_buf, upstream_wlast_buf}),
      //
      .pop_ready(downstream_wready),
      .pop_valid_unstable(downstream_wvalid),
      .pop_data_unstable({downstream_wuser, downstream_wdata, downstream_wstrb, downstream_wlast})
  );

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
