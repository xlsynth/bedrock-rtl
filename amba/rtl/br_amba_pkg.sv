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

// Bedrock-RTL AMBA Package
//
// Contains some AMBA-related definitions and helper functions.

// ri lint_check_waive FILE_NAME
package br_amba;

  // AXI response types
  typedef enum logic [1:0] {
    AxiRespOkay   = 2'b00,  // Normal access
    AxiRespExOkay = 2'b01,  // Exclusive access okay
    AxiRespSlverr = 2'b10,  // Slave error
    AxiRespDecerr = 2'b11   // Decode error
  } axi_resp_t;

  // According to AXI spec, we need to pick the worst error response (i.e., DECERR > SLVERR > OKAY).
  function automatic logic [1:0] get_worst_error_response(logic [1:0] resp1, logic [1:0] resp2);
    return (resp1 > resp2) ? resp1 : resp2;  // ri lint_check_waive ENUM_RHS
  endfunction

  // AXI Burst types
  typedef enum logic [1:0] {
    AxiBurstFixed    = 2'b00,  // Fixed burst
    AxiBurstIncr     = 2'b01,  // Incrementing burst
    AxiBurstWrap     = 2'b10,  // Wrapping burst
    AxiBurstReserved = 2'b11   // Reserved
  } axi_burst_type_t;

  // AXI parameters
  localparam int unsigned AxiCacheWidth = 4;
  localparam int unsigned AxiProtWidth = 3;
  localparam int unsigned AxiRespWidth = 2;
  localparam int unsigned AxiBurstLenWidth = 8;
  localparam int unsigned AxiBurstSizeWidth = 3;
  localparam int unsigned AxiBurstTypeWidth = 2;
  localparam int unsigned AxiWLastWidth = 1;
  localparam int unsigned AxiRLastWidth = 1;

  // APB parameters
  localparam int unsigned ApbProtWidth = 3;

  // ATB parameters
  localparam int unsigned AtbIdWidth = 7;

endpackage : br_amba
