// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_default_target_fpv_monitor #(
    parameter int DataWidth = 64,
    parameter int DecodeError = 1,
    parameter logic [DataWidth-1:0] DefaultReadData = '0
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Reduced AXI4-Lite target interface
    input logic                             target_awvalid,
    input logic                             target_awready,
    input logic                             target_wvalid,
    input logic                             target_wready,
    input logic [br_amba::AxiRespWidth-1:0] target_bresp,
    input logic                             target_bvalid,
    input logic                             target_bready,
    input logic                             target_arvalid,
    input logic                             target_arready,
    input logic [            DataWidth-1:0] target_rdata,
    input logic [br_amba::AxiRespWidth-1:0] target_rresp,
    input logic                             target_rvalid,
    input logic                             target_rready
);

  axi4_master #(
      .AXI4_LITE (1),
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
      .wuser   (),
      .wdata   (),
      .wstrb   (),
      .wlast   (),
      // Write Response channel
      .bvalid  (target_bvalid),
      .bready  (target_bready),
      .bresp   (target_bresp),
      .buser   (),
      .bid     (),
      // Read Address Channel
      .arvalid (target_arvalid),
      .arready (target_arready),
      .araddr  (),
      .aruser  (),
      .arprot  (),
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
      .rdata   (target_rdata),
      .rresp   (target_rresp),
      .ruser   (),
      .rid     (),
      .rlast   ()
  );

endmodule : br_amba_axil_default_target_fpv_monitor

bind br_amba_axil_default_target br_amba_axil_default_target_fpv_monitor #(
    .DataWidth(DataWidth),
    .DecodeError(DecodeError),
    .DefaultReadData(DefaultReadData)
) monitor (.*);
