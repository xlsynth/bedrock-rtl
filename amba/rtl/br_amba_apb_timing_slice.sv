// SPDX-License-Identifier: Apache-2.0

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

  logic psel_out_next;
  logic penable_out_next;
  logic pready_out_next;
  logic valid_handshake, valid_handshake_d1;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)

  //------------------------------------------
  // Register assignments
  //------------------------------------------

  `BR_REGN(paddr_out, paddr_in)
  `BR_REGN(pprot_out, pprot_in)
  `BR_REGN(pstrb_out, pstrb_in)
  `BR_REGN(pwrite_out, pwrite_in)
  `BR_REGN(pwdata_out, pwdata_in)
  `BR_REGN(pslverr_out, pslverr_in)
  `BR_REGN(prdata_out, prdata_in)

  `BR_REG(psel_out, psel_out_next)
  `BR_REG(penable_out, penable_out_next)
  `BR_REG(pready_out, pready_out_next)
  `BR_REG(valid_handshake_d1, valid_handshake)

  assign valid_handshake = psel_out && penable_out && pready_in;

  // Reset psel_out and penable_out when a valid handshake is detected. Need to include two cycles
  // of delay to account for the delay in the pready_out signal.
  assign psel_out_next = psel_in && !valid_handshake && !valid_handshake_d1;
  assign penable_out_next = penable_in && !valid_handshake && !valid_handshake_d1;

  // Because we are introducing delay to psel and penable, we need to reset the pready_out signal
  // to allow psel and penable to propagate to the target.
  assign pready_out_next = psel_out && penable_out && pready_in;

endmodule
