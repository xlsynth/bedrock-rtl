// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_axil_monitor_sim_pkg;
  import br_amba_axil_sim_pkg::*;

  typedef struct {
    axil_aw_t packet;
    time      timestamp;
  } axil_aw_observation_t;

  typedef struct {
    axil_w_t packet;
    time     timestamp;
  } axil_w_observation_t;

  typedef struct {
    axil_ar_t packet;
    time      timestamp;
  } axil_ar_observation_t;

  typedef struct {
    axil_b_t packet;
    time     timestamp;
    time     valid_timestamp;
  } axil_b_observation_t;

  typedef struct {
    axil_r_t packet;
    time     timestamp;
    time     valid_timestamp;
  } axil_r_observation_t;

  typedef struct {
    logic awvalid;
    logic awready;
    logic wvalid;
    logic wready;
    logic arvalid;
    logic arready;
    time  timestamp;
  } axil_request_state_observation_t;
endpackage : br_amba_axil_monitor_sim_pkg
