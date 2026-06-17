// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

package br_amba_axi_sim_pkg;

  localparam int AxiSimAddrWidth = 64;
  localparam int AxiSimDataWidth = 1024;
  localparam int AxiSimIdWidth = 16;
  localparam int AxiSimUserWidth = 64;
  localparam int AxiSimStrobeWidth = AxiSimDataWidth / 8;

  // R: rename as AxiAddrWidth etc,
  typedef struct packed {
    logic [AxiSimAddrWidth-1:0] addr;
    logic [AxiSimIdWidth-1:0] id;
    logic [AxiBurstLenWidth-1:0] len;
    logic [AxiBurstSizeWidth-1:0] size;
    logic [AxiBurstTypeWidth-1:0] burst;
    logic [AxiProtWidth-1:0] prot;
    logic [AxiSimUserWidth-1:0] user;
  } axi_aw_t;

  typedef struct packed {
    logic [AxiSimDataWidth-1:0] data;
    logic [AxiSimStrobeWidth-1:0] strb;
    logic [AxiSimUserWidth-1:0] user;
    logic last;
  } axi_w_t;

  typedef struct packed {
    logic [AxiSimAddrWidth-1:0] addr;
    logic [AxiSimIdWidth-1:0] id;
    logic [AxiBurstLenWidth-1:0] len;
    logic [AxiBurstSizeWidth-1:0] size;
    logic [AxiBurstTypeWidth-1:0] burst;
    logic [AxiProtWidth-1:0] prot;
    logic [AxiSimUserWidth-1:0] user;
  } axi_ar_t;

  typedef struct packed {
    logic [AxiSimIdWidth-1:0] id;
    logic [AxiSimUserWidth-1:0] user;
    logic [AxiRespWidth-1:0] resp;
  } axi_b_t;

  typedef struct packed {
    logic [AxiSimIdWidth-1:0] id;
    logic [AxiSimDataWidth-1:0] data;
    logic [AxiRespWidth-1:0] resp;
    logic [AxiSimUserWidth-1:0] user;
    logic last;
  } axi_r_t;

endpackage : br_amba_axi_sim_pkg
