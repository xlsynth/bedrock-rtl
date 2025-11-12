// SPDX-License-Identifier: Apache-2.0


// AXI4-Lite Default Target
//
// This module acts as an AXI4-Lite default target.
//
// The DecodeError parameter controls whether the target will respond with an
// error when an address is received that is not recognized. If DecodeError is
// 0, the target will respond with an OKAY response. If DecodeError is 1, the
// target will respond with a DECERR response.

module br_amba_axil_default_target #(
    parameter int DataWidth = 64,
    parameter int DecodeError = 1,
    parameter int SlvErr = 0,
    parameter logic [DataWidth-1:0] DefaultReadData = '0
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Reduced AXI4-Lite target interface
    input  logic                             target_awvalid,
    output logic                             target_awready,
    input  logic                             target_wvalid,
    output logic                             target_wready,
    output logic [br_amba::AxiRespWidth-1:0] target_bresp,
    output logic                             target_bvalid,
    input  logic                             target_bready,
    input  logic                             target_arvalid,
    output logic                             target_arready,
    output logic [            DataWidth-1:0] target_rdata,
    output logic [br_amba::AxiRespWidth-1:0] target_rresp,
    output logic                             target_rvalid,
    input  logic                             target_rready
);

  br_amba_axi_default_target #(
      .DataWidth(DataWidth),
      .DecodeError(DecodeError),
      .SlvErr(SlvErr),
      .DefaultReadData(DefaultReadData),
      .AxiIdWidth(1),
      .SingleBeat(1)
  ) br_amba_axi_default_target_inst (
      .clk,
      .rst,
      .target_awvalid,
      .target_awready,
      .target_awid (1'b0),
      .target_awlen(1'b0),
      .target_wvalid,
      .target_wready,
      .target_wlast(1'b1),
      .target_bresp,
      .target_bvalid,
      .target_bready,
      .target_bid  (),
      .target_arvalid,
      .target_arready,
      .target_arid (1'b0),
      .target_arlen(1'b0),
      .target_rvalid,
      .target_rready,
      .target_rdata,
      .target_rresp,
      .target_rid  (),
      .target_rlast()
  );

endmodule : br_amba_axil_default_target
