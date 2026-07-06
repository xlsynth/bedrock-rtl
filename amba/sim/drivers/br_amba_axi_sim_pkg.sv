// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_axi_sim_pkg;
  import br_amba::*;

`ifndef BR_AMBA_AXI_SIM_ADDR_WIDTH
  `define BR_AMBA_AXI_SIM_ADDR_WIDTH 64
`endif

`ifndef BR_AMBA_AXI_SIM_DATA_WIDTH
  `define BR_AMBA_AXI_SIM_DATA_WIDTH 1024
`endif

`ifndef BR_AMBA_AXI_SIM_ID_WIDTH
  `define BR_AMBA_AXI_SIM_ID_WIDTH 16
`endif

`ifndef BR_AMBA_AXI_SIM_USER_WIDTH
  `define BR_AMBA_AXI_SIM_USER_WIDTH 64
`endif

  parameter int AxiAddrWidth = `BR_AMBA_AXI_SIM_ADDR_WIDTH;
  parameter int AxiDataWidth = `BR_AMBA_AXI_SIM_DATA_WIDTH;
  parameter int AxiIdWidth = `BR_AMBA_AXI_SIM_ID_WIDTH;
  parameter int AxiUserWidth = `BR_AMBA_AXI_SIM_USER_WIDTH;
  parameter int AxiStrobeWidth = AxiDataWidth / 8;

  typedef struct packed {
    logic [AxiAddrWidth-1:0] addr;
    logic [AxiIdWidth-1:0] id;
    logic [AxiBurstLenWidth-1:0] len;
    logic [AxiBurstSizeWidth-1:0] size;
    logic [AxiBurstTypeWidth-1:0] burst;
    logic [AxiProtWidth-1:0] prot;
    logic [AxiUserWidth-1:0] user;
  } axi_aw_t;

  typedef struct packed {
    logic [AxiDataWidth-1:0] data;
    logic [AxiStrobeWidth-1:0] strb;
    logic [AxiUserWidth-1:0] user;
    logic last;
  } axi_w_t;

  typedef struct packed {
    logic [AxiAddrWidth-1:0] addr;
    logic [AxiIdWidth-1:0] id;
    logic [AxiBurstLenWidth-1:0] len;
    logic [AxiBurstSizeWidth-1:0] size;
    logic [AxiBurstTypeWidth-1:0] burst;
    logic [AxiProtWidth-1:0] prot;
    logic [AxiUserWidth-1:0] user;
  } axi_ar_t;

  typedef struct packed {
    logic [AxiIdWidth-1:0]   id;
    logic [AxiUserWidth-1:0] user;
    logic [AxiRespWidth-1:0] resp;
  } axi_b_t;

  typedef struct packed {
    logic [AxiIdWidth-1:0] id;
    logic [AxiDataWidth-1:0] data;
    logic [AxiRespWidth-1:0] resp;
    logic [AxiUserWidth-1:0] user;
    logic last;
  } axi_r_t;

  typedef struct packed {
    axi_aw_t payload;
    logic valid;
  } axi_aw_source_t;

  typedef struct packed {
    axi_w_t payload;
    logic   valid;
  } axi_w_source_t;

  typedef struct packed {
    axi_ar_t payload;
    logic valid;
  } axi_ar_source_t;

  function automatic logic [AxiBurstLenWidth-1:0] get_axi_default_target_aw_len(
      input int index, input bit single_beat, input int max_len);
    if (single_beat) begin
      get_axi_default_target_aw_len = '0;
    end else begin
      get_axi_default_target_aw_len = AxiBurstLenWidth'(index % (max_len + 1));
    end
  endfunction

  function automatic logic [AxiBurstLenWidth-1:0] get_axi_default_target_ar_len(
      input int index, input bit single_beat, input int max_len);
    if (single_beat) begin
      get_axi_default_target_ar_len = '0;
    end else begin
      get_axi_default_target_ar_len = AxiBurstLenWidth'((index % max_len) + 1);
    end
  endfunction

endpackage : br_amba_axi_sim_pkg
