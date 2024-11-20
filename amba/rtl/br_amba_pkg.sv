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

// Bedrock-RTL AMBA Package
//
// Contains some AMBA-related definitions and helper functions.

package br_amba_pkg;

  // AXI response types
  typedef enum logic [1:0] {
    AxiRespOkay   = 2'b00,  // Normal access
    AxiRespExOkay = 2'b01,  // Exclusive access okay
    AxiRespSlverr = 2'b10,  // Slave error
    AxiRespDecerr = 2'b11   // Decode error
  } axi_resp_t;

  // AXI parameters
  localparam int unsigned AxiProtWidth = 3;
  localparam int unsigned AxiRespWidth = 2;

  // APB parameters
  localparam int unsigned ApbProtWidth = 3;

endpackage : br_amba_pkg
