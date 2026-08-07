// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_axil_split_sim_pkg;
  import br_amba::*;
  import br_amba_axil_sim_pkg::*;

  typedef enum bit {
    AxilSplitRouteTrunk,
    AxilSplitRouteBranch
  } axil_split_route_t;

  typedef enum int {
    AxilSplitTransactionWrite,
    AxilSplitTransactionRead
  } axil_split_transaction_kind_t;

  typedef enum int {
    AxilResetTriggerAwBeforeW,
    AxilResetTriggerWBeforeAw,
    AxilResetTriggerBPending,
    AxilResetTriggerRPending
  } axil_reset_trigger_t;

  typedef struct packed {
    axil_split_transaction_kind_t kind;
    axil_split_route_t            route;
    logic [AxilAddrWidth-1:0]     root_addr;
    logic [AxilAddrWidth-1:0]     routed_addr;
    logic [AxiProtWidth-1:0]      prot;
    logic [AxilUserWidth-1:0]     addr_user;
    logic [AxilDataWidth-1:0]     data;
    logic [AxilStrobeWidth-1:0]   strb;
    logic [AxilUserWidth-1:0]     data_user;
    logic [AxiRespWidth-1:0]      resp;
    logic [AxilUserWidth-1:0]     response_user;
    time                          request_ts;
    time                          response_ts;
  } axil_split_transaction_t;

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
    int   max_trunk_ready_stall_cycles;
    int   max_branch_ready_stall_cycles;
    logic allow_error_responses;
    logic force_trunk_route;
    logic force_branch_route;
    logic check_max_outstanding_reads;
    logic check_max_outstanding_writes;
  } axil_split_scenario_t;

  typedef struct {
    int root_aw;
    int root_w;
    int root_ar;
    int root_b;
    int root_r;
    int trunk_aw;
    int trunk_w;
    int trunk_ar;
    int trunk_b;
    int trunk_r;
    int branch_aw;
    int branch_w;
    int branch_ar;
    int branch_b;
    int branch_r;
  } axil_reset_counts_t;
endpackage : br_amba_axil_split_sim_pkg
