// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

package br_amba_apb_sim_pkg;
  localparam logic Psel0 = 1'b0;
  localparam logic Psel1 = 1'b1;
  localparam logic Penable0 = 1'b0;
  localparam logic Penable1 = 1'b1;
  localparam logic Pready0 = 1'b0;
  localparam logic Pready1 = 1'b1;
  localparam logic Pslverr0 = 1'b0;

  typedef struct packed {
    logic [31:0] addr;
    logic [ApbProtWidth-1:0] prot;
    logic [3:0] strb;
    logic write;
    logic [31:0] wdata;
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
    logic [31:0] rdata;
    logic slverr;
  } apb_response_t;

  typedef struct {
    int num_transactions;
    int wait_cycles;
  } apb_response_controls_t;
endpackage : br_amba_apb_sim_pkg
