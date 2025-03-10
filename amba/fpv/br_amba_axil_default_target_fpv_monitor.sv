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

// AXI4-Lite Default Target FPV checks

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
      .awuser  ('d0),
      .awaddr  ('d0),
      .awprot  ('d0),
      .awid    ('d0),
      .awlen   ('d0),
      .awsize  (),                // (DataWidth> 8) ? $clog2(DataWidth/8) : 1
      .awburst ('d0),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      // Write Channel
      .wvalid  (target_wvalid),
      .wready  (target_wready),
      .wuser   ('d0),
      .wdata   ('d0),
      .wstrb   ('d0),
      .wlast   ('d1),
      // Write Response channel
      .bvalid  (target_bvalid),
      .bready  (target_bready),
      .buser   ('d0),
      .bresp   (target_bresp),
      .bid     ('d0),
      // Read Address Channel
      .arvalid (target_arvalid),
      .arready (target_arready),
      .araddr  ('d0),
      .aruser  ('d0),
      .arprot  ('d0),
      .arid    ('d0),
      .arlen   ('d0),
      .arsize  (),                // (DataWidth> 8) ? $clog2(DataWidth/8) : 1
      .arburst ('d0),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      // Read Channel
      .rvalid  (target_rvalid),
      .rready  (target_rready),
      .ruser   ('d0),
      .rdata   (target_rdata),
      .rresp   (target_rresp),
      .rid     ('d0),
      .rlast   ('d1)
  );

endmodule : br_amba_axil_default_target_fpv_monitor

bind br_amba_axil_default_target br_amba_axil_default_target_fpv_monitor #(
    .DataWidth(DataWidth),
    .DecodeError(DecodeError),
    .DefaultReadData(DefaultReadData)
) monitor (.*);
