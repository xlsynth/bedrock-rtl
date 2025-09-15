// SPDX-License-Identifier: Apache-2.0


// This module acts as an AXI4 default target.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi_default_target_fpv_monitor #(
    parameter int DataWidth = 64,
    parameter bit DecodeError = 1,
    parameter bit SlvErr = 0,
    parameter int AxiIdWidth = 1,
    parameter bit SingleBeat = 0,
    parameter logic [DataWidth-1:0] DefaultReadData = '0,
    localparam int AxiLenWidth = SingleBeat ? 1 : br_amba::AxiBurstLenWidth
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Reduced AXI4-Lite target interface
    input logic                             target_awvalid,
    input logic                             target_awready,
    input logic [           AxiIdWidth-1:0] target_awid,
    input logic [          AxiLenWidth-1:0] target_awlen,
    input logic                             target_wvalid,
    input logic                             target_wready,
    input logic                             target_wlast,
    input logic                             target_bvalid,
    input logic                             target_bready,
    input logic [           AxiIdWidth-1:0] target_bid,
    input logic [br_amba::AxiRespWidth-1:0] target_bresp,
    input logic                             target_arvalid,
    input logic                             target_arready,
    input logic [           AxiIdWidth-1:0] target_arid,
    input logic [          AxiLenWidth-1:0] target_arlen,
    input logic                             target_rvalid,
    input logic                             target_rready,
    input logic [            DataWidth-1:0] target_rdata,
    input logic [br_amba::AxiRespWidth-1:0] target_rresp,
    input logic [           AxiIdWidth-1:0] target_rid,
    input logic                             target_rlast
);

  if (SingleBeat) begin : gen_asm
    `BR_ASSUME(single_beat_arlen_a, target_arvalid |-> target_arlen == 'b0)
    `BR_ASSUME(single_beat_awlen_a, target_awvalid |-> target_awlen == 'b0)
    `BR_ASSUME(single_beat_wlast_a, target_wvalid |-> target_wlast == 'b1)
  end

  axi4_master #(
      .ID_WIDTH(AxiIdWidth),
      .LEN_WIDTH(AxiLenWidth),
      .BRESP_WIDTH(br_amba::AxiRespWidth),
      .DATA_WIDTH(DataWidth)
  ) root (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (target_awvalid),
      .awready (target_awready),
      .awuser  (),
      .awaddr  (),
      .awprot  (),
      .awid    (target_awid),
      .awlen   (target_awlen),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (target_wvalid),
      .wready  (target_wready),
      .wuser   (),
      .wdata   (),
      .wstrb   (),
      .wlast   (target_wlast),
      // Write Response channel
      .bvalid  (target_bvalid),
      .bready  (target_bready),
      .bresp   (target_bresp),
      .buser   ('d0),
      .bid     (target_bid),
      // Read Address Channel
      .arvalid (target_arvalid),
      .arready (target_arready),
      .araddr  (),
      .aruser  (),
      .arprot  (),
      .arid    (target_arid),
      .arlen   (target_arlen),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (target_rvalid),
      .rready  (target_rready),
      .rdata   (target_rdata),
      .rresp   (target_rresp),
      .ruser   ('d0),
      .rid     (target_rid),
      .rlast   (target_rlast)
  );

endmodule : br_amba_axi_default_target_fpv_monitor

bind br_amba_axi_default_target br_amba_axi_default_target_fpv_monitor #(
    .DataWidth(DataWidth),
    .DecodeError(DecodeError),
    .SlvErr(SlvErr),
    .AxiIdWidth(AxiIdWidth),
    .SingleBeat(SingleBeat),
    .DefaultReadData(DefaultReadData)
) monitor (.*);
