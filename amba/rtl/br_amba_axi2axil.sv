// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL AXI4 to AXI4-Lite Bridge
//
// Converts an AXI4 interface to an AXI4-Lite interface.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_amba_axi2axil #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be at least 32
    parameter int IdWidth = 4,  // Must be at least 1
    parameter int AWUserWidth = 8,  // Must be at least 1
    parameter int ARUserWidth = 8,  // Must be at least 1
    parameter int WUserWidth = 8,  // Must be at least 1
    parameter int BUserWidth = 8,  // Must be at least 1
    parameter int RUserWidth = 8,  // Must be at least 1
    localparam int StrbWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input  logic [            AddrWidth-1:0] axi_awaddr,
    input  logic [              IdWidth-1:0] axi_awid,
    input  logic [            UserWidth-1:0] axi_awuser,
    input  logic [br_amba::AxiProtWidth-1:0] axi_awprot,
    input  logic                             axi_awvalid,
    output logic                             axi_awready,
    input  logic [            DataWidth-1:0] axi_wdata,
    input  logic [        (DataWidth/8)-1:0] axi_wstrb,
    input  logic                             axi_wvalid,
    output logic                             axi_wready,
    output logic [              IdWidth-1:0] axi_bid,
    output logic [            UserWidth-1:0] axi_buser,
    output logic                             axi_bvalid,
    input  logic                             axi_bready,
    input  logic [            AddrWidth-1:0] axi_araddr,
    input  logic [              IdWidth-1:0] axi_arid,
    input  logic [            UserWidth-1:0] axi_aruser,
    input  logic [br_amba::AxiProtWidth-1:0] axi_arprot,
    input  logic                             axi_arvalid,
    output logic                             axi_arready,
    output logic [              IdWidth-1:0] axi_rid,
    output logic [            UserWidth-1:0] axi_ruser,
    output logic                             axi_rvalid,
    input  logic                             axi_rready,

    // AXI4-Lite interface
    input  logic [            AddrWidth-1:0] axil_awaddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input  logic                             axil_awvalid,
    output logic                             axil_awready,
    input  logic [            DataWidth-1:0] axil_wdata,
    input  logic [        (DataWidth/8)-1:0] axil_wstrb,
    input  logic                             axil_wvalid,
    output logic                             axil_wready,
    output logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    output logic                             axil_bvalid,
    input  logic                             axil_bready,
    input  logic [            AddrWidth-1:0] axil_araddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    input  logic                             axil_arvalid,
    output logic                             axil_arready,
    output logic [            DataWidth-1:0] axil_rdata,
    output logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    output logic                             axil_rvalid,
    input  logic                             axil_rready
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_32_or_64_a, (DataWidth == 32) || (DataWidth == 64))
  `BR_ASSERT_STATIC(id_width_must_be_at_least_1_a, IdWidth >= 1)
  `BR_ASSERT_STATIC(awuser_width_must_be_at_least_1_a, AWUserWidth >= 1)
  `BR_ASSERT_STATIC(aruser_width_must_be_at_least_1_a, ARUserWidth >= 1)
  `BR_ASSERT_STATIC(wuser_width_must_be_at_least_1_a, WUserWidth >= 1)
  `BR_ASSERT_STATIC(buser_width_must_be_at_least_1_a, BUserWidth >= 1)
  `BR_ASSERT_STATIC(ruser_width_must_be_at_least_1_a, RUserWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

endmodule : br_amba_axi2axil
