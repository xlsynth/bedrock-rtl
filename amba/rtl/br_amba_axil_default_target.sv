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
    parameter int DataWidth   = 64,
    parameter int DecodeError = 1
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
  logic aw_handshake, w_handshake, ar_handshake, b_handshake, r_handshake;

  // Handshake signals
  assign aw_handshake = target_awvalid && target_awready;
  assign w_handshake = target_wvalid && target_wready;
  assign ar_handshake = target_arvalid && target_arready;
  assign b_handshake = target_bvalid && target_bready;
  assign r_handshake = target_rvalid && target_rready;

  // Response signals
  assign target_bresp = DecodeError ? br_amba::AxiRespDecerr : br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_RHS CONST_ASSIGN CONST_OUTPUT
  assign target_rdata = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  assign target_rresp = DecodeError ? br_amba::AxiRespDecerr : br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_RHS CONST_ASSIGN CONST_OUTPUT

  // Write address & data channel
  always_ff @(posedge clk) begin
    if (rst) begin
      target_awready <= 1'b0;
      target_wready  <= 1'b0;
    end else begin
      target_awready <= !target_bvalid && !target_awready && target_awvalid && target_wvalid;
      target_wready  <= !target_bvalid && !target_wready && target_awvalid && target_wvalid;
    end
  end

  // Write response channel
  always_ff @(posedge clk) begin
    if (rst) begin
      target_bvalid <= 1'b0;
    end else if (aw_handshake && w_handshake) begin
      target_bvalid <= 1'b1;
    end else if (b_handshake) begin
      target_bvalid <= 1'b0;
    end
  end

  // Read address channel
  always_ff @(posedge clk) begin
    if (rst) begin
      target_arready <= 1'b0;
    end else begin
      target_arready <= !target_arready && target_arvalid;
    end
  end

  // Read data channel
  always_ff @(posedge clk) begin
    if (rst) begin
      target_rvalid <= 1'b0;
    end else if (ar_handshake) begin
      target_rvalid <= 1'b1;
    end else if (r_handshake) begin
      target_rvalid <= 1'b0;
    end
  end

endmodule : br_amba_axil_default_target
