// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_axil_sim_pkg;
  import br_amba::*;

  localparam int AxilAddrWidth = 64;
  localparam int AxilDataWidth = 1024;
  localparam int AxilUserWidth = 64;
  localparam int AxilStrobeWidth = AxilDataWidth / 8;

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
