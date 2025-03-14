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

// Bedrock-RTL APB Timing Slice

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_apb_timing_slice_fpv_monitor #(
    parameter int AddrWidth = 12  // Must be at least 12
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Upstream APB interface
    input logic [            AddrWidth-1:0] paddr_in,
    input logic                             psel_in,
    input logic                             penable_in,
    input logic [br_amba::ApbProtWidth-1:0] pprot_in,
    input logic [                      3:0] pstrb_in,
    input logic                             pwrite_in,
    input logic [                     31:0] pwdata_in,
    input logic [                     31:0] prdata_out,
    input logic                             pready_out,
    input logic                             pslverr_out,

    // Downstream APB interface
    input logic [            AddrWidth-1:0] paddr_out,
    input logic                             psel_out,
    input logic                             penable_out,
    input logic [br_amba::ApbProtWidth-1:0] pprot_out,
    input logic [                      3:0] pstrb_out,
    input logic                             pwrite_out,
    input logic [                     31:0] pwdata_out,
    input logic [                     31:0] prdata_in,
    input logic                             pready_in,
    input logic                             pslverr_in
);

  // Upstream APB interface
  apb4_master #(
      .ABUS_WIDTH(AddrWidth)
  ) upstream (
      .pclk(clk),
      .presetn(!rst),
      .psel(psel_in),
      .penable(penable_in),
      .paddr(paddr_in),
      .pwrite(pwrite_in),
      .pwdata(pwdata_in),
      .pstrb(pstrb_in),
      .pprot(pprot_in),
      .pready(pready_out),
      .prdata(prdata_out),
      .pslverr(pslverr_out)
  );

  // Downstream APB interface
  apb4_slave #(
      .ABUS_WIDTH(AddrWidth)
  ) downstream (
      .pclk(clk),
      .presetn(!rst),
      .psel(psel_out),
      .penable(penable_out),
      .paddr(paddr_out),
      .pwrite(pwrite_out),
      .pwdata(pwdata_out),
      .pstrb(pstrb_out),
      .pprot(pprot_out),
      .pready(pready_in),
      .prdata(prdata_in),
      .pslverr(pslverr_in)
  );

endmodule : br_amba_apb_timing_slice_fpv_monitor

bind br_amba_apb_timing_slice br_amba_apb_timing_slice_fpv_monitor #(
    .AddrWidth(AddrWidth)
) monitor (.*);
