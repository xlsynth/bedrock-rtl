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

  // Internal signals
  logic awfifo_pop_valid, awfifo_pop_ready;
  logic wfifo_pop_valid, wfifo_pop_ready;

  // Response signals
  assign target_bresp = DecodeError ? br_amba::AxiRespDecerr : br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_RHS CONST_ASSIGN CONST_OUTPUT
  assign target_rdata = DefaultReadData;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  assign target_rresp = DecodeError ? br_amba::AxiRespDecerr : br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_RHS CONST_ASSIGN CONST_OUTPUT

  // Write address channel
  br_flow_reg_fwd #(
      .Width(1)
  ) br_flow_reg_fwd_aw (
      .clk,
      .rst,

      .push_ready(target_awready),
      .push_valid(target_awvalid),
      .push_data (1'b0),

      .pop_ready(awfifo_pop_ready),
      .pop_valid(awfifo_pop_valid),
      .pop_data()  // ri lint_check_waive OPEN_OUTPUT
  );

  // Only pop from write address channel when write response is ready and valid
  assign awfifo_pop_ready = target_bready && target_bvalid;

  // Write data channel
  br_flow_reg_fwd #(
      .Width(1)
  ) br_flow_reg_fwd_w (
      .clk,
      .rst,

      .push_ready(target_wready),
      .push_valid(target_wvalid),
      .push_data (1'b0),

      .pop_ready(wfifo_pop_ready),
      .pop_valid(wfifo_pop_valid),
      .pop_data()  // ri lint_check_waive OPEN_OUTPUT
  );

  // Only pop from write data channel when write response is ready and valid
  assign wfifo_pop_ready = target_bready && target_bvalid;

  // Generate write response when both address and data channels have valid signals
  assign target_bvalid   = awfifo_pop_valid && wfifo_pop_valid;

  // Read address and response channels
  br_flow_reg_fwd #(
      .Width(1)
  ) br_flow_reg_fwd_ar (
      .clk,
      .rst,

      .push_ready(target_arready),
      .push_valid(target_arvalid),
      .push_data (1'b0),

      .pop_ready(target_rready),
      .pop_valid(target_rvalid),
      .pop_data()  // ri lint_check_waive OPEN_OUTPUT
  );

endmodule : br_amba_axil_default_target
