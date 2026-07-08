// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_axil2apb_sim_pkg;
  import br_amba::*;
  import br_amba_apb_sim_pkg::*;

  typedef enum int {
    Axil2ApbTransactionWrite,
    Axil2ApbTransactionRead
  } axil2apb_transaction_kind_t;

  typedef struct packed {
    axil2apb_transaction_kind_t kind;
    logic [ApbAddrWidth-1:0]    addr;
    logic [AxiProtWidth-1:0]    prot;
    logic [ApbStrbWidth-1:0]    strb;
    logic [ApbDataWidth-1:0]    data;
    logic                       slverr;
  } axil2apb_transaction_t;

  typedef struct {
    int   num_writes;
    int   num_reads;
    int   min_aw_gap_cycles;
    int   max_aw_gap_cycles;
    int   min_w_gap_cycles;
    int   max_w_gap_cycles;
    int   min_ar_gap_cycles;
    int   max_ar_gap_cycles;
    int   min_b_stall_cycles;
    int   max_b_stall_cycles;
    int   min_r_stall_cycles;
    int   max_r_stall_cycles;
    int   apb_wait_cycles;
    logic allow_slverr;
    logic force_slverr;
  } axil2apb_scenario_t;
endpackage : br_amba_axil2apb_sim_pkg
