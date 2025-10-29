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

// AXI4-Lite Timing Slice

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_timing_slice_fpv_monitor #(
    parameter  int AddrWidth   = 40,
    parameter  int DataWidth   = 64,
    parameter  int AWUserWidth = 1,
    parameter  int WUserWidth  = 1,
    parameter  int ARUserWidth = 1,
    parameter  int RUserWidth  = 1,
    parameter  int BUserWidth  = 1,
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite target interface
    input logic [            AddrWidth-1:0] target_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] target_awprot,
    input logic [          AWUserWidth-1:0] target_awuser,
    input logic                             target_awvalid,
    input logic                             target_awready,
    input logic [            DataWidth-1:0] target_wdata,
    input logic [          StrobeWidth-1:0] target_wstrb,
    input logic [           WUserWidth-1:0] target_wuser,
    input logic                             target_wvalid,
    input logic                             target_wready,
    input logic [br_amba::AxiRespWidth-1:0] target_bresp,
    input logic [           BUserWidth-1:0] target_buser,
    input logic                             target_bvalid,
    input logic                             target_bready,
    input logic [            AddrWidth-1:0] target_araddr,
    input logic [br_amba::AxiProtWidth-1:0] target_arprot,
    input logic [          ARUserWidth-1:0] target_aruser,
    input logic                             target_arvalid,
    input logic                             target_arready,
    input logic [            DataWidth-1:0] target_rdata,
    input logic [br_amba::AxiRespWidth-1:0] target_rresp,
    input logic [           RUserWidth-1:0] target_ruser,
    input logic                             target_rvalid,
    input logic                             target_rready,

    // AXI4-Lite initiator interface
    input logic [            AddrWidth-1:0] init_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] init_awprot,
    input logic [          AWUserWidth-1:0] init_awuser,
    input logic                             init_awvalid,
    input logic                             init_awready,
    input logic [            DataWidth-1:0] init_wdata,
    input logic [          StrobeWidth-1:0] init_wstrb,
    input logic [           WUserWidth-1:0] init_wuser,
    input logic                             init_wvalid,
    input logic                             init_wready,
    input logic [br_amba::AxiRespWidth-1:0] init_bresp,
    input logic [           BUserWidth-1:0] init_buser,
    input logic                             init_bvalid,
    input logic                             init_bready,
    input logic [            AddrWidth-1:0] init_araddr,
    input logic [br_amba::AxiProtWidth-1:0] init_arprot,
    input logic [          ARUserWidth-1:0] init_aruser,
    input logic                             init_arvalid,
    input logic                             init_arready,
    input logic [            DataWidth-1:0] init_rdata,
    input logic [br_amba::AxiRespWidth-1:0] init_rresp,
    input logic [           RUserWidth-1:0] init_ruser,
    input logic                             init_rvalid,
    input logic                             init_rready
);

  // ABVIP should send more than DUT to test backpressure
  localparam int MaxInit = 2;
  localparam int MaxTarget = MaxInit + 2;
  localparam int AwPayloadWidth = AddrWidth + br_amba::AxiProtWidth + AWUserWidth;
  localparam int WPayloadWidth = DataWidth + StrobeWidth + WUserWidth;
  localparam int BPayloadWidth = BUserWidth + br_amba::AxiRespWidth;
  localparam int ARPayloadWidth = AddrWidth + br_amba::AxiProtWidth + ARUserWidth;
  localparam int RPayloadWidth = DataWidth + RUserWidth + br_amba::AxiRespWidth;

  // AXI4-Lite target interface
  axi4_master #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .CONFIG_WDATA_MASKED(0),
      .MAX_PENDING(MaxTarget),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) target (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (target_awvalid),
      .awready (target_awready),
      .awuser  (target_awuser),
      .awaddr  (target_awaddr),
      .awprot  (target_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (target_wvalid),
      .wready  (target_wready),
      .wuser   (target_wuser),
      .wdata   (target_wdata),
      .wstrb   (target_wstrb),
      .wlast   (),
      // Write Response channel
      .bvalid  (target_bvalid),
      .bready  (target_bready),
      .buser   (target_buser),
      .bresp   (target_bresp),
      .bid     (),
      // Read Address Channel
      .arvalid (target_arvalid),
      .arready (target_arready),
      .araddr  (target_araddr),
      .aruser  (target_aruser),
      .arprot  (target_arprot),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (target_rvalid),
      .rready  (target_rready),
      .ruser   (target_ruser),
      .rdata   (target_rdata),
      .rresp   (target_rresp),
      .rid     (),
      .rlast   ()
  );

  // AXI4-Lite initiator interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .CONFIG_RDATA_MASKED(0),
      .MAX_PENDING(MaxInit),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) init (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (init_awvalid),
      .awready (init_awready),
      .awuser  (init_awuser),
      .awaddr  (init_awaddr),
      .awprot  (init_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (init_wvalid),
      .wready  (init_wready),
      .wuser   (init_wuser),
      .wdata   (init_wdata),
      .wstrb   (init_wstrb),
      .wlast   (),
      // Write Response channel
      .bvalid  (init_bvalid),
      .bready  (init_bready),
      .buser   (init_buser),
      .bresp   (init_bresp),
      .bid     (),
      // Read Address Channel
      .arvalid (init_arvalid),
      .arready (init_arready),
      .araddr  (init_araddr),
      .aruser  (init_aruser),
      .arprot  (init_arprot),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (init_rvalid),
      .rready  (init_rready),
      .ruser   (init_ruser),
      .rdata   (init_rdata),
      .rresp   (init_rresp),
      .rid     (),
      .rlast   ()
  );

  // ----------across target and init, no command is dropped or reordered----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(AwPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxTarget)
  ) aw_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(target_awvalid & target_awready),
      .incoming_data({target_awaddr, target_awprot, target_awuser}),
      .outgoing_vld(init_awvalid & init_awready),
      .outgoing_data({init_awaddr, init_awprot, init_awuser})
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(WPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxTarget)
  ) w_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(target_wvalid & target_wready),
      .incoming_data({target_wdata, target_wstrb, target_wuser}),
      .outgoing_vld(init_wvalid & init_wready),
      .outgoing_data({init_wdata, init_wstrb, init_wuser})
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(BPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxTarget)
  ) b_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(init_bvalid & init_bready),
      .incoming_data({init_bresp, init_buser}),
      .outgoing_vld(target_bvalid & target_bready),
      .outgoing_data({target_bresp, target_buser})
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ARPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxTarget)
  ) ar_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(target_arvalid & target_arready),
      .incoming_data({target_araddr, target_arprot, target_aruser}),
      .outgoing_vld(init_arvalid & init_arready),
      .outgoing_data({init_araddr, init_arprot, init_aruser})
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(RPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxTarget)
  ) r_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(init_rvalid & init_rready),
      .incoming_data({init_rdata, init_rresp, init_ruser}),
      .outgoing_vld(target_rvalid & target_rready),
      .outgoing_data({target_rdata, target_rresp, target_ruser})
  );

endmodule : br_amba_axil_timing_slice_fpv_monitor

bind br_amba_axil_timing_slice br_amba_axil_timing_slice_fpv_monitor #(
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth (WUserWidth),
    .RUserWidth (RUserWidth)
) monitor (.*);
