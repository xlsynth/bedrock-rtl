// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

`include "br_asserts.svh"

package br_amba_axil_sim_pkg;
  import br_amba::*;

`ifndef BR_AMBA_AXIL_SIM_ADDR_WIDTH
  `define BR_AMBA_AXIL_SIM_ADDR_WIDTH 64
`endif

`ifndef BR_AMBA_AXIL_SIM_DATA_WIDTH
  `define BR_AMBA_AXIL_SIM_DATA_WIDTH 1024
`endif

`ifndef BR_AMBA_AXIL_SIM_USER_WIDTH
  `define BR_AMBA_AXIL_SIM_USER_WIDTH 64
`endif

  parameter int AxilAddrWidth = `BR_AMBA_AXIL_SIM_ADDR_WIDTH;
  parameter int AxilDataWidth = `BR_AMBA_AXIL_SIM_DATA_WIDTH;
  parameter int AxilUserWidth = `BR_AMBA_AXIL_SIM_USER_WIDTH;
  localparam int AxilStrobeWidth = AxilDataWidth / 8;

  `BR_ASSERT_STATIC_IN_PACKAGE(AxilAddrWidthPositive, AxilAddrWidth > 0)
  `BR_ASSERT_STATIC_IN_PACKAGE(AxilDataWidthPositive, AxilDataWidth > 0)
  `BR_ASSERT_STATIC_IN_PACKAGE(AxilDataWidthByteAligned, AxilDataWidth % 8 == 0)
  `BR_ASSERT_STATIC_IN_PACKAGE(AxilUserWidthPositive, AxilUserWidth > 0)

  typedef struct packed {
    logic [AxilAddrWidth-1:0] addr;
    logic [AxiProtWidth-1:0]  prot;
    logic [AxilUserWidth-1:0] user;
  } axil_aw_t;

  typedef struct packed {
    logic [AxilDataWidth-1:0]   data;
    logic [AxilStrobeWidth-1:0] strb;
    logic [AxilUserWidth-1:0]   user;
  } axil_w_t;

  typedef struct packed {
    logic [AxilAddrWidth-1:0] addr;
    logic [AxiProtWidth-1:0]  prot;
    logic [AxilUserWidth-1:0] user;
  } axil_ar_t;

  typedef struct packed {
    logic [AxiRespWidth-1:0]  resp;
    logic [AxilUserWidth-1:0] user;
  } axil_b_t;

  typedef struct packed {
    logic [AxilDataWidth-1:0] data;
    logic [AxiRespWidth-1:0]  resp;
    logic [AxilUserWidth-1:0] user;
  } axil_r_t;

  typedef enum int {
    AxilRequestAw,
    AxilRequestW,
    AxilRequestAr
  } axil_request_channel_t;

  typedef enum int {
    AxilTransactionWrite,
    AxilTransactionRead
  } axil_transaction_kind_t;

  typedef enum int {
    AxilHandshakeAw,
    AxilHandshakeW,
    AxilHandshakeB,
    AxilHandshakeAr,
    AxilHandshakeR
  } axil_handshake_channel_t;

  typedef struct {
    logic [AxilAddrWidth-1:0] addr;
    logic [AxiProtWidth-1:0]  prot;
    int                       gap_cycles;
  } axil_aw_driver_item_t;

  typedef struct {
    logic [AxilDataWidth-1:0]   data;
    logic [AxilStrobeWidth-1:0] strb;
    int                         gap_cycles;
  } axil_w_driver_item_t;

  typedef struct {
    logic [AxilAddrWidth-1:0] addr;
    logic [AxiProtWidth-1:0]  prot;
    int                       gap_cycles;
  } axil_ar_driver_item_t;

endpackage : br_amba_axil_sim_pkg
