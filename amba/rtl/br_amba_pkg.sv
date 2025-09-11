// SPDX-License-Identifier: Apache-2.0

package br_amba;

  // AXI response types
  typedef enum logic [1:0] {
    AxiRespOkay   = 2'b00,  // Normal access
    AxiRespExOkay = 2'b01,  // Exclusive access okay
    AxiRespSlverr = 2'b10,  // Slave error
    AxiRespDecerr = 2'b11   // Decode error
  } axi_resp_t;

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
