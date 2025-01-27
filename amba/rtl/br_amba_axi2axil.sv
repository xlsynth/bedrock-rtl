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
// Converts an AXI4 interface to an AXI4-Lite interface. This module supports FIXED and INCR bursts.
// It does not support WRAP bursts. AXI4 burst transactions will be split into multiple AXI4-Lite
// transactions. All write responses will be aggregated into a single AXI4 write response.
//

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_amba_axi2axil #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be at least 32
    parameter int IdWidth = 4,  // Must be at least 1
    parameter int AWUserWidth = 8,  // Must be at least 1
    parameter int ARUserWidth = 8,  // Must be at least 1
    parameter int WUserWidth = 8,  // Must be at least 1
    parameter int BUserWidth = 8,  // Must be at least 1
    parameter int RUserWidth = 8,  // Must be at least 1
    parameter int MaxOutstandingReqs = 16,  // Must be at least 2
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input  logic [                 AddrWidth-1:0] axi_awaddr,
    input  logic [                   IdWidth-1:0] axi_awid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_awburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_awprot,
    input  logic [               AWUserWidth-1:0] axi_awuser,
    input  logic                                  axi_awvalid,
    output logic                                  axi_awready,
    input  logic [                 DataWidth-1:0] axi_wdata,
    input  logic [               StrobeWidth-1:0] axi_wstrb,
    input  logic [                WUserWidth-1:0] axi_wuser,
    input  logic                                  axi_wlast,
    input  logic                                  axi_wvalid,
    output logic                                  axi_wready,
    output logic [                   IdWidth-1:0] axi_bid,
    output logic [                BUserWidth-1:0] axi_buser,
    output logic [     br_amba::AxiRespWidth-1:0] axi_bresp,
    output logic                                  axi_bvalid,
    input  logic                                  axi_bready,
    input  logic [                 AddrWidth-1:0] axi_araddr,
    input  logic [                   IdWidth-1:0] axi_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_arprot,
    input  logic [               ARUserWidth-1:0] axi_aruser,
    input  logic                                  axi_arvalid,
    output logic                                  axi_arready,
    output logic [                   IdWidth-1:0] axi_rid,
    output logic [                 DataWidth-1:0] axi_rdata,
    output logic [                RUserWidth-1:0] axi_ruser,
    output logic [     br_amba::AxiRespWidth-1:0] axi_rresp,
    output logic                                  axi_rlast,
    output logic                                  axi_rvalid,
    input  logic                                  axi_rready,

    // AXI4-Lite interface
    output logic [            AddrWidth-1:0] axil_awaddr,
    output logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    output logic [          AWUserWidth-1:0] axil_awuser,
    output logic                             axil_awvalid,
    input  logic                             axil_awready,
    output logic [            DataWidth-1:0] axil_wdata,
    output logic [          StrobeWidth-1:0] axil_wstrb,
    output logic [           WUserWidth-1:0] axil_wuser,
    output logic                             axil_wvalid,
    input  logic                             axil_wready,
    input  logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input  logic [           BUserWidth-1:0] axil_buser,
    input  logic                             axil_bvalid,
    output logic                             axil_bready,
    output logic [            AddrWidth-1:0] axil_araddr,
    output logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    output logic [          ARUserWidth-1:0] axil_aruser,
    output logic                             axil_arvalid,
    input  logic                             axil_arready,
    input  logic [            DataWidth-1:0] axil_rdata,
    input  logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    input  logic [           RUserWidth-1:0] axil_ruser,
    input  logic                             axil_rvalid,
    output logic                             axil_rready
);

  //----------------------------------------------------------------------------
  // Integration checks
  //----------------------------------------------------------------------------

  // ri lint_check_off GENERATE_NAME
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_32_or_64_a, (DataWidth == 32) || (DataWidth == 64))
  `BR_ASSERT_STATIC(id_width_must_be_at_least_1_a, IdWidth >= 1)
  `BR_ASSERT_STATIC(awuser_width_must_be_at_least_1_a, AWUserWidth >= 1)
  `BR_ASSERT_STATIC(aruser_width_must_be_at_least_1_a, ARUserWidth >= 1)
  `BR_ASSERT_STATIC(wuser_width_must_be_at_least_1_a, WUserWidth >= 1)
  `BR_ASSERT_STATIC(buser_width_must_be_at_least_1_a, BUserWidth >= 1)
  `BR_ASSERT_STATIC(ruser_width_must_be_at_least_1_a, RUserWidth >= 1)
  `BR_ASSERT_STATIC(max_outstanding_reqs_must_be_at_least_2_a, MaxOutstandingReqs >= 2)
  // ri lint_check_on GENERATE_NAME

  //----------------------------------------------------------------------------
  // Implementation
  //----------------------------------------------------------------------------

  br_amba_axi2axil_core #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .ReqUserWidth(AWUserWidth),
      .RespUserWidth(BUserWidth),
      .ReqDataUserWidth(WUserWidth),
      .IsReadNotWrite(0),
      .MaxOutstandingReqs(MaxOutstandingReqs)
  ) br_amba_axi2axil_core_write (
      .clk,
      .rst,

      // AXI4 interface
      .axi_req_addr(axi_awaddr),
      .axi_req_id(axi_awid),
      .axi_req_len(axi_awlen),
      .axi_req_size(axi_awsize),
      .axi_req_burst(axi_awburst),
      .axi_req_prot(axi_awprot),
      .axi_req_user(axi_awuser),
      .axi_req_valid(axi_awvalid),
      .axi_req_ready(axi_awready),

      .axi_req_data(axi_wdata),
      .axi_req_data_strb(axi_wstrb),
      .axi_req_data_user(axi_wuser),
      .axi_req_data_last(axi_wlast),
      .axi_req_data_valid(axi_wvalid),
      .axi_req_data_ready(axi_wready),

      .axi_resp_id(axi_bid),
      .axi_resp_user(axi_buser),
      .axi_resp_resp(axi_bresp),
      .axi_resp_data(),  // not used for writes
      .axi_resp_data_last(),  // not used for writes
      .axi_resp_valid(axi_bvalid),
      .axi_resp_ready(axi_bready),

      // AXI4-Lite interface
      .axil_req_addr (axil_awaddr),
      .axil_req_prot (axil_awprot),
      .axil_req_user (axil_awuser),
      .axil_req_valid(axil_awvalid),
      .axil_req_ready(axil_awready),

      .axil_req_data(axil_wdata),
      .axil_req_data_strb(axil_wstrb),
      .axil_req_data_user(axil_wuser),
      .axil_req_data_valid(axil_wvalid),
      .axil_req_data_ready(axil_wready),

      .axil_resp_resp (axil_bresp),
      .axil_resp_user (axil_buser),
      .axil_resp_data ({DataWidth{1'b0}}),  // not used for writes
      .axil_resp_valid(axil_bvalid),
      .axil_resp_ready(axil_bready)
  );

  br_amba_axi2axil_core #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .ReqUserWidth(ARUserWidth),
      .RespUserWidth(RUserWidth),
      .ReqDataUserWidth(1),
      .IsReadNotWrite(1),
      .MaxOutstandingReqs(MaxOutstandingReqs)
  ) br_amba_axi2axil_core_read (
      .clk,
      .rst,

      // AXI4 interface
      .axi_req_addr(axi_araddr),
      .axi_req_id(axi_arid),
      .axi_req_len(axi_arlen),
      .axi_req_size(axi_arsize),
      .axi_req_burst(axi_arburst),
      .axi_req_prot(axi_arprot),
      .axi_req_user(axi_aruser),
      .axi_req_valid(axi_arvalid),
      .axi_req_ready(axi_arready),

      .axi_req_data({DataWidth{1'b0}}),  // not used for reads
      .axi_req_data_strb({StrobeWidth{1'b0}}),  // not used for reads
      .axi_req_data_user(1'b0),  // not used for reads
      .axi_req_data_last(1'b0),  // not used for reads
      .axi_req_data_valid(1'b0),  // not used for reads
      .axi_req_data_ready(),  // not used for reads

      .axi_resp_id(axi_rid),
      .axi_resp_user(axi_ruser),
      .axi_resp_resp(axi_rresp),
      .axi_resp_data(axi_rdata),
      .axi_resp_data_last(axi_rlast),
      .axi_resp_valid(axi_rvalid),
      .axi_resp_ready(axi_rready),

      // AXI4-Lite interface
      .axil_req_addr (axil_araddr),
      .axil_req_prot (axil_arprot),
      .axil_req_user (axil_aruser),
      .axil_req_valid(axil_arvalid),
      .axil_req_ready(axil_arready),

      .axil_req_data(),  // not used for reads
      .axil_req_data_strb(),  // not used for reads
      .axil_req_data_user(),  // not used for reads
      .axil_req_data_valid(),  // not used for reads
      .axil_req_data_ready(1'b0),  // not used for reads

      .axil_resp_resp (axil_rresp),
      .axil_resp_user (axil_ruser),
      .axil_resp_data (axil_rdata),
      .axil_resp_valid(axil_rvalid),
      .axil_resp_ready(axil_rready)
  );

endmodule : br_amba_axi2axil
