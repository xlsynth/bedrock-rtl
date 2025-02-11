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
//
// An APB timing slice to help with timing closure.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_amba_apb_timing_slice #(
    parameter int AddrWidth = 12  // Must be at least 12
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Upstream APB interface
    input  logic [            AddrWidth-1:0] paddr_in,
    input  logic                             psel_in,
    input  logic                             penable_in,
    input  logic [br_amba::ApbProtWidth-1:0] pprot_in,
    input  logic [                      3:0] pstrb_in,
    input  logic                             pwrite_in,
    input  logic [                     31:0] pwdata_in,
    output logic [                     31:0] prdata_out,
    output logic                             pready_out,
    output logic                             pslverr_out,

    // Downstream APB interface
    output logic [            AddrWidth-1:0] paddr_out,
    output logic                             psel_out,
    output logic                             penable_out,
    output logic [br_amba::ApbProtWidth-1:0] pprot_out,
    output logic [                      3:0] pstrb_out,
    output logic                             pwrite_out,
    output logic [                     31:0] pwdata_out,
    input  logic [                     31:0] prdata_in,
    input  logic                             pready_in,
    input  logic                             pslverr_in
);

  logic pready_out_next;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)

  //------------------------------------------
  // Register assignments
  //------------------------------------------

  `BR_REG(paddr_out, paddr_in)
  `BR_REG(pprot_out, pprot_in)
  `BR_REG(pstrb_out, pstrb_in)
  `BR_REG(pwrite_out, pwrite_in)
  `BR_REG(pwdata_out, pwdata_in)
  `BR_REG(psel_out, psel_in)
  `BR_REG(penable_out, penable_in)
  `BR_REG(pslverr_out, pslverr_in)
  `BR_REG(prdata_out, prdata_in)
  `BR_REG(pready_out, pready_out_next)

  // Because we are introducing delay to psel and penable, we need to reset the pready_out signal
  // to allow psel and penable to propagate to the target.
  assign pready_out_next = (psel_in && ~penable_in) ? 1'b0 :
                           (psel_out && penable_out) ? pready_in :
                           pready_out;

endmodule
