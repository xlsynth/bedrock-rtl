// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

package br_amba_axi_sim_pkg;

  localparam int AxiAddrWidth = 64;
  localparam int AxiDataWidth = 1024;
  localparam int AxiIdWidth = 16;
  localparam int AxiUserWidth = 64;
  localparam int AxiStrobeWidth = AxiDataWidth / 8;

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

  function automatic logic [255:0] get_axi_payload_pattern(input int index, input int salt,
                                                           input logic [31:0] payload_seed);
    for (int word = 0; word < 8; word++) begin
      get_axi_payload_pattern[word*32+:32] = 32'((index + 1) * (salt + (word * 17)) ^
                                                 (payload_seed >> (word % 7)) ^
                                                 (32'h1020_4081 << (word % 5)));
    end
  endfunction

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

  function automatic axi_aw_t get_axi_default_target_aw_input(
      input int index, input bit single_beat, input int max_len, input int strobe_width);
    get_axi_default_target_aw_input = '0;
    get_axi_default_target_aw_input.addr = AxiAddrWidth'(32'h1000 + index);
    get_axi_default_target_aw_input.id = AxiIdWidth'(index + 1);
    get_axi_default_target_aw_input.len =
        get_axi_default_target_aw_len(index, single_beat, max_len);
    get_axi_default_target_aw_input.size = AxiBurstSizeWidth'($clog2(strobe_width));
    get_axi_default_target_aw_input.burst = AxiBurstIncr;
  endfunction

  function automatic axi_w_t get_axi_default_target_w_input(input int index);
    get_axi_default_target_w_input = '0;
    get_axi_default_target_w_input.data = AxiDataWidth'(32'hcafe_0000 + index);
    get_axi_default_target_w_input.strb = '1;
    get_axi_default_target_w_input.last = 1'b1;
  endfunction

  function automatic axi_ar_t get_axi_default_target_ar_input(
      input int index, input bit single_beat, input int max_len, input int strobe_width);
    get_axi_default_target_ar_input = '0;
    get_axi_default_target_ar_input.addr = AxiAddrWidth'(32'h2000 + index);
    get_axi_default_target_ar_input.id = AxiIdWidth'(index + 1);
    get_axi_default_target_ar_input.len =
        get_axi_default_target_ar_len(index, single_beat, max_len);
    get_axi_default_target_ar_input.size = AxiBurstSizeWidth'($clog2(strobe_width));
    get_axi_default_target_ar_input.burst = AxiBurstIncr;
  endfunction

  function automatic axi_aw_t get_axi_timing_slice_aw_input(input int index, input int strobe_width,
                                                            input logic [31:0] payload_seed);
    logic [255:0] payload;

    payload = get_axi_payload_pattern(index, 11, payload_seed);
    get_axi_timing_slice_aw_input.addr  = payload[AxiAddrWidth-1:0];
    get_axi_timing_slice_aw_input.id    = payload[32+:AxiIdWidth];
    get_axi_timing_slice_aw_input.len   = AxiBurstLenWidth'(index);
    get_axi_timing_slice_aw_input.size  = AxiBurstSizeWidth'($clog2(strobe_width));
    get_axi_timing_slice_aw_input.burst = AxiBurstIncr;
    get_axi_timing_slice_aw_input.prot  = payload[64+:AxiProtWidth];
    get_axi_timing_slice_aw_input.user  = payload[96+:AxiUserWidth];
  endfunction

  function automatic axi_w_t get_axi_timing_slice_w_input(input int index,
                                                          input logic [31:0] payload_seed);
    logic [255:0] payload;

    payload = get_axi_payload_pattern(index, 23, payload_seed);
    get_axi_timing_slice_w_input.data = '0;
    get_axi_timing_slice_w_input.data[255:0] = payload;
    get_axi_timing_slice_w_input.strb = payload[128+:AxiStrobeWidth] | AxiStrobeWidth'(1'b1);
    get_axi_timing_slice_w_input.user = payload[160+:AxiUserWidth];
    get_axi_timing_slice_w_input.last = index[0];
  endfunction

  function automatic axi_ar_t get_axi_timing_slice_ar_input(input int index, input int strobe_width,
                                                            input logic [31:0] payload_seed);
    logic [255:0] payload;

    payload = get_axi_payload_pattern(index, 37, payload_seed);
    get_axi_timing_slice_ar_input.addr  = payload[AxiAddrWidth-1:0];
    get_axi_timing_slice_ar_input.id    = payload[32+:AxiIdWidth];
    get_axi_timing_slice_ar_input.len   = AxiBurstLenWidth'(index + 1);
    get_axi_timing_slice_ar_input.size  = AxiBurstSizeWidth'($clog2(strobe_width));
    get_axi_timing_slice_ar_input.burst = AxiBurstWrap;
    get_axi_timing_slice_ar_input.prot  = payload[64+:AxiProtWidth];
    get_axi_timing_slice_ar_input.user  = payload[96+:AxiUserWidth];
  endfunction

  function automatic axi_b_t get_axi_timing_slice_b_input(input int index,
                                                          input logic [31:0] payload_seed);
    logic [255:0] payload;

    payload = get_axi_payload_pattern(index, 47, payload_seed);
    get_axi_timing_slice_b_input.id = payload[AxiIdWidth-1:0];
    get_axi_timing_slice_b_input.user = payload[32+:AxiUserWidth];
    get_axi_timing_slice_b_input.resp = AxiRespWidth'(index);
  endfunction

  function automatic axi_r_t get_axi_timing_slice_r_input(input int index,
                                                          input logic [31:0] payload_seed);
    logic [255:0] payload;

    payload = get_axi_payload_pattern(index, 59, payload_seed);
    get_axi_timing_slice_r_input.id = payload[AxiIdWidth-1:0];
    get_axi_timing_slice_r_input.data = '0;
    get_axi_timing_slice_r_input.data[255:0] = payload;
    get_axi_timing_slice_r_input.resp = AxiRespWidth'(index + 1);
    get_axi_timing_slice_r_input.user = payload[160+:AxiUserWidth];
    get_axi_timing_slice_r_input.last = !index[0];
  endfunction

endpackage : br_amba_axi_sim_pkg
