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

module br_amba_atb_funnel_fpv_monitor #(
    parameter int NumSources = 2,  // Must be at least 2
    parameter int DataWidth = 32,  // Must be at least 1
    parameter int UserWidth = 1,  // Must be at least 1
    localparam int ByteCountWidth = $clog2(DataWidth / 8)
) (
    input logic clk,
    input logic rst,

    // ATB source interfaces
    input logic [NumSources-1:0] src_atvalid,
    input logic [NumSources-1:0] src_atready,
    input logic [NumSources-1:0][br_amba::AtbIdWidth-1:0] src_atid,
    input logic [NumSources-1:0][DataWidth-1:0] src_atdata,
    input logic [NumSources-1:0][ByteCountWidth-1:0] src_atbytes,
    input logic [NumSources-1:0][UserWidth-1:0] src_atuser,
    // ATB destination interface
    input logic dst_atvalid,
    input logic dst_atready,
    input logic [br_amba::AtbIdWidth-1:0] dst_atid,
    input logic [DataWidth-1:0] dst_atdata,
    input logic [ByteCountWidth-1:0] dst_atbytes,
    input logic [UserWidth-1:0] dst_atuser
);

  // ATB source interfaces
  for (genvar i = 0; i < NumSources; i++) begin : gen_src
    // ABVIP doesn't have atuser field
    `BR_ASSUME(atuser_stable_a, src_atvalid[i] && !src_atready[i] |=> $stable(src_atuser[i]))
    // ABVIP properties are encrypted, so not possible to debug why assumptions are not working
    `BR_ASSUME(atdata_stable_a, src_atvalid[i] && !src_atready[i] |=> $stable(src_atdata[i]))

    cdn_abvip_amba_atb_master #(
        .DATA_WIDTH(DataWidth),
        .ID_WIDTH(br_amba::AtbIdWidth),
        .BYTES_WIDTH(ByteCountWidth)
    ) src (
        .atclk   (clk),
        .atclken (1'b1),
        .atresetn(!rst),
        .atdata  (src_atdata[i]),
        .atbytes (src_atbytes[i]),
        .atid    (src_atid[i]),
        .atvalid (src_atvalid[i]),
        .atready (src_atready[i])
    );
  end

  // ATB destination interface
  cdn_abvip_amba_atb_slave #(
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(br_amba::AtbIdWidth),
      .BYTES_WIDTH(ByteCountWidth)
  ) dst (
      .atclk   (clk),
      .atclken (1'b1),
      .atresetn(!rst),
      .atdata  (dst_atdata),
      .atbytes (dst_atbytes),
      .atid    (dst_atid),
      .atvalid (dst_atvalid),
      .atready (dst_atready)
  );

endmodule : br_amba_atb_funnel_fpv_monitor

bind br_amba_atb_funnel br_amba_atb_funnel_fpv_monitor #(
    .NumSources(NumSources),
    .DataWidth (DataWidth),
    .UserWidth (UserWidth)
) monitor (.*);
