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

// AXI4-Lite Timing Slice
//
// This module creates a timing slice on an AXI4-Lite interface.

module br_amba_axil_timing_slice #(
    parameter int AddrWidth   = 40,
    parameter int DataWidth   = 64,
    parameter int AWUserWidth = 1,
    parameter int WUserWidth  = 1,
    parameter int ARUserWidth = 1,
    parameter int RUserWidth  = 1
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite target interface
    input  logic [    AddrWidth-1:0] tgt_awaddr,
    input  logic [              2:0] tgt_awprot,
    input  logic [  AWUserWidth-1:0] tgt_awuser,
    input  logic                     tgt_awvalid,
    output logic                     tgt_awready,
    input  logic [    DataWidth-1:0] tgt_wdata,
    input  logic [(DataWidth/8)-1:0] tgt_wstrb,
    input  logic [   WUserWidth-1:0] tgt_wuser,
    input  logic                     tgt_wvalid,
    output logic                     tgt_wready,
    output logic [              1:0] tgt_bresp,
    output logic                     tgt_bvalid,
    input  logic                     tgt_bready,
    input  logic [    AddrWidth-1:0] tgt_araddr,
    input  logic [              2:0] tgt_arprot,
    input  logic [  ARUserWidth-1:0] tgt_aruser,
    input  logic                     tgt_arvalid,
    output logic                     tgt_arready,
    output logic [    DataWidth-1:0] tgt_rdata,
    output logic [              1:0] tgt_rresp,
    output logic [   RUserWidth-1:0] tgt_ruser,
    output logic                     tgt_rvalid,
    input  logic                     tgt_rready,

    // AXI4-Lite initiator interface
    output logic [    AddrWidth-1:0] init_awaddr,
    output logic [              2:0] init_awprot,
    output logic [  AWUserWidth-1:0] init_awuser,
    output logic                     init_awvalid,
    input  logic                     init_awready,
    output logic [    DataWidth-1:0] init_wdata,
    output logic [(DataWidth/8)-1:0] init_wstrb,
    output logic [   WUserWidth-1:0] init_wuser,
    output logic                     init_wvalid,
    input  logic                     init_wready,
    input  logic [              1:0] init_bresp,
    input  logic                     init_bvalid,
    output logic                     init_bready,
    output logic [    AddrWidth-1:0] init_araddr,
    output logic [              2:0] init_arprot,
    output logic [  ARUserWidth-1:0] init_aruser,
    output logic                     init_arvalid,
    input  logic                     init_arready,
    input  logic [    DataWidth-1:0] init_rdata,
    input  logic [              1:0] init_rresp,
    input  logic [   RUserWidth-1:0] init_ruser,
    input  logic                     init_rvalid,
    output logic                     init_rready
);

  // Write Address Channel Timing Slice
  br_flow_reg_both #(
      .Width(AddrWidth + 3 + AWUserWidth)  // Address + Prot + User
  ) aw_slice (
      .clk,
      .rst,
      .push_ready(tgt_awready),
      .push_valid(tgt_awvalid),
      .push_data ({tgt_awaddr, tgt_awprot, tgt_awuser}),
      .pop_ready (init_awready),
      .pop_valid (init_awvalid),
      .pop_data  ({init_awaddr, init_awprot, init_awuser})
  );

  // Write Data Channel Timing Slice
  br_flow_reg_both #(
      .Width(DataWidth + WUserWidth + (DataWidth / 8))  // Data + Wstrb + User
  ) w_slice (
      .clk,
      .rst,
      .push_ready(tgt_wready),
      .push_valid(tgt_wvalid),
      .push_data ({tgt_wdata, tgt_wstrb, tgt_wuser}),
      .pop_ready (init_wready),
      .pop_valid (init_wvalid),
      .pop_data  ({init_wdata, init_wstrb, init_wuser})
  );

  // Write Response Channel Timing Slice
  br_flow_reg_both #(
      .Width(2)  // Response (2 bits)
  ) b_slice (
      .clk,
      .rst,
      .push_ready(init_bready),
      .push_valid(init_bvalid),
      .push_data (init_bresp),
      .pop_ready (tgt_bready),
      .pop_valid (tgt_bvalid),
      .pop_data  (tgt_bresp)
  );

  // Read Address Channel Timing Slice
  br_flow_reg_both #(
      .Width(AddrWidth + 3 + RUserWidth)  // Address + Prot + User
  ) ar_slice (
      .clk,
      .rst,
      .push_ready(tgt_arready),
      .push_valid(tgt_arvalid),
      .push_data ({tgt_araddr, tgt_arprot, tgt_aruser}),
      .pop_ready (init_arready),
      .pop_valid (init_arvalid),
      .pop_data  ({init_araddr, init_arprot, init_aruser})
  );

  // Read Data Channel Timing Slice
  br_flow_reg_both #(
      .Width(DataWidth + 2 + RUserWidth)  // Data + Response (2 bits) + User
  ) r_slice (
      .clk,
      .rst,
      .push_ready(init_rready),
      .push_valid(init_rvalid),
      .push_data ({init_rdata, init_rresp, init_ruser}),
      .pop_ready (tgt_rready),
      .pop_valid (tgt_rvalid),
      .pop_data  ({tgt_rdata, tgt_rresp, tgt_ruser})
  );

endmodule : br_amba_axil_timing_slice
