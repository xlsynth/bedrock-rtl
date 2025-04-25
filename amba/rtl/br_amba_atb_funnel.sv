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

// Bedrock-RTL ATB Funnel
//
// Uses round-robin arbitration to funnel requests from multiple ATB
// sources to a single ATB destination.

`include "br_asserts_internal.svh"

module br_amba_atb_funnel #(
    parameter int NumSources = 2,  // Must be at least 2
    parameter int DataWidth = 32,  // Must be at least 1
    parameter int UserWidth = 1,  // Must be at least 1
    // If 1, ensure that the dst_atready signal is registered. This ensures there is no
    // combinational path from dst_atready to src_atready.
    parameter bit RegisterAtReady = 0,
    localparam int ByteCountWidth = $clog2(DataWidth / 8)
) (
    input logic clk,
    input logic rst,

    // ATB source interfaces
    input logic [NumSources-1:0] src_atvalid,
    output logic [NumSources-1:0] src_atready,
    input logic [NumSources-1:0][br_amba::AtbIdWidth-1:0] src_atid,
    input logic [NumSources-1:0][DataWidth-1:0] src_atdata,
    input logic [NumSources-1:0][ByteCountWidth-1:0] src_atbytes,
    input logic [NumSources-1:0][UserWidth-1:0] src_atuser,
    // ATB destination interface
    output logic dst_atvalid,
    input logic dst_atready,
    output logic [br_amba::AtbIdWidth-1:0] dst_atid,
    output logic [DataWidth-1:0] dst_atdata,
    output logic [ByteCountWidth-1:0] dst_atbytes,
    output logic [UserWidth-1:0] dst_atuser
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_sources_gte_2_a, NumSources >= 2)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(userwidth_gte_1_a, UserWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  localparam int PacketWidth = br_amba::AtbIdWidth + DataWidth + ByteCountWidth + UserWidth;

  logic [NumSources-1:0][PacketWidth-1:0] src_packet;

  // Pack the source ATB signals into a single packet
  for (genvar i = 0; i < NumSources; i++) begin : gen_src_packet
    assign src_packet[i] = {src_atid[i], src_atdata[i], src_atbytes[i], src_atuser[i]};
  end

  br_flow_mux_rr_stable #(
      .NumFlows(NumSources),
      .Width(PacketWidth),
      .RegisterPopReady(RegisterAtReady)
  ) br_flow_mux_rr_stable (
      .clk(clk),
      .rst(rst),
      .push_valid(src_atvalid),
      .push_ready(src_atready),
      .push_data(src_packet),
      .pop_valid(dst_atvalid),
      .pop_ready(dst_atready),
      .pop_data({dst_atid, dst_atdata, dst_atbytes, dst_atuser})
  );

endmodule : br_amba_atb_funnel
