// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

`include "br_asserts.svh"

package br_amba_apb_sim_pkg;
  import br_amba::*;

`ifndef BR_AMBA_APB_SIM_ADDR_WIDTH
  `define BR_AMBA_APB_SIM_ADDR_WIDTH 64
`endif

`ifndef BR_AMBA_APB_SIM_DATA_WIDTH
  `define BR_AMBA_APB_SIM_DATA_WIDTH 1024
`endif

  parameter int ApbAddrWidth = `BR_AMBA_APB_SIM_ADDR_WIDTH;
  parameter int ApbDataWidth = `BR_AMBA_APB_SIM_DATA_WIDTH;
  localparam int ApbStrbWidth = ApbDataWidth / 8;

  `BR_ASSERT_STATIC_IN_PACKAGE(ApbAddrWidthPositive, ApbAddrWidth > 0)
  `BR_ASSERT_STATIC_IN_PACKAGE(ApbDataWidthPositive, ApbDataWidth > 0)
  `BR_ASSERT_STATIC_IN_PACKAGE(ApbDataWidthByteAligned, ApbDataWidth % 8 == 0)

  localparam logic Psel0 = 1'b0;
  localparam logic Psel1 = 1'b1;
  localparam logic Penable0 = 1'b0;
  localparam logic Penable1 = 1'b1;
  localparam logic Pready0 = 1'b0;
  localparam logic Pready1 = 1'b1;
  localparam logic Pslverr0 = 1'b0;
  localparam logic Pslverr1 = 1'b1;

  typedef struct packed {
    logic [ApbAddrWidth-1:0] addr;
    logic [ApbProtWidth-1:0] prot;
    logic [ApbStrbWidth-1:0] strb;
    logic write;
    logic [ApbDataWidth-1:0] wdata;
  } apb_request_t;

  typedef struct packed {
    logic psel;
    logic penable;
    apb_request_t request;
  } apb_request_beat_t;

  typedef struct {
    int num_transactions;
    int setup_cycles;
    int idle_cycles;
  } apb_request_controls_t;

  typedef struct packed {
    logic ready;
    logic [ApbDataWidth-1:0] rdata;
    logic slverr;
  } apb_response_t;

  typedef struct packed {
    logic [ApbAddrWidth-1:0] addr;
    logic [ApbProtWidth-1:0] prot;
    logic [ApbStrbWidth-1:0] strb;
    logic write;
    logic [ApbDataWidth-1:0] data;
    logic slverr;
  } apb_transfer_t;

  typedef struct {
    apb_transfer_t packet;
    time           request_timestamp;
    time           completion_timestamp;
  } apb_transfer_observation_t;

  typedef struct {
    int num_transactions;
    int wait_cycles;
  } apb_response_controls_t;
endpackage : br_amba_apb_sim_pkg
