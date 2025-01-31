// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// AXI4 Timing Slice
//
// This module creates a timing slice for all 5 channels of on an
// AXI4 interface. There is a per-channel parameter to choose between
// forward, reverse, or full timing slices.
//

`include "br_asserts_internal.svh"

module br_amba_axi_timing_slice #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be 32, 64, or 128
    parameter int IdWidth = 1,  // Must be at least 1
    parameter int AWUserWidth = 1,  // Must be at least 1
    parameter int WUserWidth = 1,  // Must be at least 1
    parameter int ARUserWidth = 1,  // Must be at least 1
    parameter int BUserWidth = 1,  // Must be at least 1
    parameter int RUserWidth = 1,  // Must be at least 1
    parameter int AWSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int WSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int ARSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int RSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int BSliceType = 2,  // 0: forward, 1: reverse, 2: full
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 target interface
    input  logic [                 AddrWidth-1:0] target_awaddr,
    input  logic [                   IdWidth-1:0] target_awid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] target_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] target_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] target_awburst,
    input  logic [     br_amba::AxiProtWidth-1:0] target_awprot,
    input  logic [               AWUserWidth-1:0] target_awuser,
    input  logic                                  target_awvalid,
    output logic                                  target_awready,
    input  logic [                 DataWidth-1:0] target_wdata,
    input  logic [               StrobeWidth-1:0] target_wstrb,
    input  logic [                WUserWidth-1:0] target_wuser,
    input  logic                                  target_wlast,
    input  logic                                  target_wvalid,
    output logic                                  target_wready,
    output logic [                   IdWidth-1:0] target_bid,
    output logic [                BUserWidth-1:0] target_buser,
    output logic [     br_amba::AxiRespWidth-1:0] target_bresp,
    output logic                                  target_bvalid,
    input  logic                                  target_bready,
    input  logic [                 AddrWidth-1:0] target_araddr,
    input  logic [                   IdWidth-1:0] target_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] target_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] target_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] target_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] target_arprot,
    input  logic [               ARUserWidth-1:0] target_aruser,
    input  logic                                  target_arvalid,
    output logic                                  target_arready,
    output logic [                   IdWidth-1:0] target_rid,
    output logic [                 DataWidth-1:0] target_rdata,
    output logic [                RUserWidth-1:0] target_ruser,
    output logic [     br_amba::AxiRespWidth-1:0] target_rresp,
    output logic                                  target_rlast,
    output logic                                  target_rvalid,
    input  logic                                  target_rready,

    // AXI4 initiator interface
    output logic [                 AddrWidth-1:0] init_awaddr,
    output logic [                   IdWidth-1:0] init_awid,
    output logic [ br_amba::AxiBurstLenWidth-1:0] init_awlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] init_awsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] init_awburst,
    output logic [     br_amba::AxiProtWidth-1:0] init_awprot,
    output logic [               AWUserWidth-1:0] init_awuser,
    output logic                                  init_awvalid,
    input  logic                                  init_awready,
    output logic [                 DataWidth-1:0] init_wdata,
    output logic [               StrobeWidth-1:0] init_wstrb,
    output logic [                WUserWidth-1:0] init_wuser,
    output logic                                  init_wlast,
    output logic                                  init_wvalid,
    input  logic                                  init_wready,
    input  logic [                   IdWidth-1:0] init_bid,
    input  logic [                BUserWidth-1:0] init_buser,
    input  logic [     br_amba::AxiRespWidth-1:0] init_bresp,
    input  logic                                  init_bvalid,
    output logic                                  init_bready,
    output logic [                 AddrWidth-1:0] init_araddr,
    output logic [                   IdWidth-1:0] init_arid,
    output logic [ br_amba::AxiBurstLenWidth-1:0] init_arlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] init_arsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] init_arburst,
    output logic [     br_amba::AxiProtWidth-1:0] init_arprot,
    output logic [               ARUserWidth-1:0] init_aruser,
    output logic                                  init_arvalid,
    input  logic                                  init_arready,
    input  logic [                   IdWidth-1:0] init_rid,
    input  logic [                 DataWidth-1:0] init_rdata,
    input  logic [                RUserWidth-1:0] init_ruser,
    input  logic [     br_amba::AxiRespWidth-1:0] init_rresp,
    input  logic                                  init_rlast,
    input  logic                                  init_rvalid,
    output logic                                  init_rready
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_32_64_128_a,
                    (DataWidth == 32) || (DataWidth == 64) || (DataWidth == 128))
  `BR_ASSERT_STATIC(id_width_must_be_at_least_1_a, IdWidth >= 1)
  `BR_ASSERT_STATIC(awuser_width_must_be_at_least_1_a, AWUserWidth >= 1)
  `BR_ASSERT_STATIC(wuser_width_must_be_at_least_1_a, WUserWidth >= 1)
  `BR_ASSERT_STATIC(aruser_width_must_be_at_least_1_a, ARUserWidth >= 1)
  `BR_ASSERT_STATIC(buser_width_must_be_at_least_1_a, BUserWidth >= 1)
  `BR_ASSERT_STATIC(ruser_width_must_be_at_least_1_a, RUserWidth >= 1)
  `BR_ASSERT_STATIC(aw_slice_type_must_be_0_1_2_a,
                    (AWSliceType == 0) || (AWSliceType == 1) || (AWSliceType == 2))
  `BR_ASSERT_STATIC(w_slice_type_must_be_0_1_2_a,
                    (WSliceType == 0) || (WSliceType == 1) || (WSliceType == 2))
  `BR_ASSERT_STATIC(ar_slice_type_must_be_0_1_2_a,
                    (ARSliceType == 0) || (ARSliceType == 1) || (ARSliceType == 2))
  `BR_ASSERT_STATIC(r_slice_type_must_be_0_1_2_a,
                    (RSliceType == 0) || (RSliceType == 1) || (RSliceType == 2))
  `BR_ASSERT_STATIC(b_slice_type_must_be_0_1_2_a,
                    (BSliceType == 0) || (BSliceType == 1) || (BSliceType == 2))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Write Address Channel Timing Slice
  if (AWSliceType == 0) begin : gen_aw_slice_forward
    br_flow_reg_fwd #(
        .Width(
        AddrWidth +
        IdWidth +
        br_amba::AxiBurstLenWidth +
        br_amba::AxiBurstSizeWidth +
        br_amba::AxiBurstTypeWidth +
        br_amba::AxiProtWidth +
        AWUserWidth
      )
    ) br_flow_reg_fwd_aw_slice (
        .clk,
        .rst,
        .push_ready(target_awready),
        .push_valid(target_awvalid),
        .push_data({
          target_awaddr,
          target_awid,
          target_awlen,
          target_awsize,
          target_awburst,
          target_awprot,
          target_awuser
        }),
        .pop_ready(init_awready),
        .pop_valid(init_awvalid),
        .pop_data({
          init_awaddr, init_awid, init_awlen, init_awsize, init_awburst, init_awprot, init_awuser
        })
    );
  end : gen_aw_slice_forward

  if (AWSliceType == 1) begin : gen_aw_slice_reverse
    br_flow_reg_rev #(
        .Width(
        AddrWidth +
        IdWidth +
        br_amba::AxiBurstLenWidth +
        br_amba::AxiBurstSizeWidth +
        br_amba::AxiBurstTypeWidth +
        br_amba::AxiProtWidth +
        AWUserWidth
      )
    ) br_flow_reg_rev_aw_slice (
        .clk,
        .rst,
        .push_ready(target_awready),
        .push_valid(target_awvalid),
        .push_data({
          target_awaddr,
          target_awid,
          target_awlen,
          target_awsize,
          target_awburst,
          target_awprot,
          target_awuser
        }),
        .pop_ready(init_awready),
        .pop_valid(init_awvalid),
        .pop_data({
          init_awaddr, init_awid, init_awlen, init_awsize, init_awburst, init_awprot, init_awuser
        })
    );
  end : gen_aw_slice_reverse

  if (AWSliceType == 2) begin : gen_aw_slice_full
    br_flow_reg_both #(
        .Width(
        AddrWidth +
        IdWidth +
        br_amba::AxiBurstLenWidth +
        br_amba::AxiBurstSizeWidth +
        br_amba::AxiBurstTypeWidth +
        br_amba::AxiProtWidth +
        AWUserWidth
      )
    ) br_flow_reg_both_aw_slice (
        .clk,
        .rst,
        .push_ready(target_awready),
        .push_valid(target_awvalid),
        .push_data({
          target_awaddr,
          target_awid,
          target_awlen,
          target_awsize,
          target_awburst,
          target_awprot,
          target_awuser
        }),
        .pop_ready(init_awready),
        .pop_valid(init_awvalid),
        .pop_data({
          init_awaddr, init_awid, init_awlen, init_awsize, init_awburst, init_awprot, init_awuser
        })
    );
  end : gen_aw_slice_full

  // Write Data Channel Timing Slice
  if (WSliceType == 0) begin : gen_w_slice_forward
    br_flow_reg_fwd #(
        .Width(DataWidth + WUserWidth + StrobeWidth + br_amba::AxiWLastWidth)
    ) br_flow_reg_fwd_w_slice (
        .clk,
        .rst,
        .push_ready(target_wready),
        .push_valid(target_wvalid),
        .push_data ({target_wdata, target_wstrb, target_wuser, target_wlast}),
        .pop_ready (init_wready),
        .pop_valid (init_wvalid),
        .pop_data  ({init_wdata, init_wstrb, init_wuser, init_wlast})
    );
  end : gen_w_slice_forward

  if (WSliceType == 1) begin : gen_w_slice_reverse
    br_flow_reg_rev #(
        .Width(DataWidth + WUserWidth + StrobeWidth + br_amba::AxiWLastWidth)
    ) br_flow_reg_rev_w_slice (
        .clk,
        .rst,
        .push_ready(target_wready),
        .push_valid(target_wvalid),
        .push_data ({target_wdata, target_wstrb, target_wuser, target_wlast}),
        .pop_ready (init_wready),
        .pop_valid (init_wvalid),
        .pop_data  ({init_wdata, init_wstrb, init_wuser, init_wlast})
    );
  end : gen_w_slice_reverse

  if (WSliceType == 2) begin : gen_w_slice_full
    br_flow_reg_both #(
        .Width(DataWidth + WUserWidth + StrobeWidth + br_amba::AxiWLastWidth)
    ) br_flow_reg_both_w_slice (
        .clk,
        .rst,
        .push_ready(target_wready),
        .push_valid(target_wvalid),
        .push_data ({target_wdata, target_wstrb, target_wuser, target_wlast}),
        .pop_ready (init_wready),
        .pop_valid (init_wvalid),
        .pop_data  ({init_wdata, init_wstrb, init_wuser, init_wlast})
    );
  end : gen_w_slice_full

  // Write Response Channel Timing Slice
  if (BSliceType == 0) begin : gen_b_slice_forward
    br_flow_reg_fwd #(
        .Width(IdWidth + BUserWidth + br_amba::AxiRespWidth)
    ) br_flow_reg_fwd_b_slice (
        .clk,
        .rst,
        .push_ready(init_bready),
        .push_valid(init_bvalid),
        .push_data ({init_bid, init_buser, init_bresp}),
        .pop_ready (target_bready),
        .pop_valid (target_bvalid),
        .pop_data  ({target_bid, target_buser, target_bresp})
    );
  end : gen_b_slice_forward

  if (BSliceType == 1) begin : gen_b_slice_reverse
    br_flow_reg_rev #(
        .Width(IdWidth + BUserWidth + br_amba::AxiRespWidth)
    ) br_flow_reg_rev_b_slice (
        .clk,
        .rst,
        .push_ready(init_bready),
        .push_valid(init_bvalid),
        .push_data ({init_bid, init_buser, init_bresp}),
        .pop_ready (target_bready),
        .pop_valid (target_bvalid),
        .pop_data  ({target_bid, target_buser, target_bresp})
    );
  end : gen_b_slice_reverse

  if (BSliceType == 2) begin : gen_b_slice_full
    br_flow_reg_both #(
        .Width(IdWidth + BUserWidth + br_amba::AxiRespWidth)
    ) br_flow_reg_both_b_slice (
        .clk,
        .rst,
        .push_ready(init_bready),
        .push_valid(init_bvalid),
        .push_data ({init_bid, init_buser, init_bresp}),
        .pop_ready (target_bready),
        .pop_valid (target_bvalid),
        .pop_data  ({target_bid, target_buser, target_bresp})
    );
  end : gen_b_slice_full

  // Read Address Channel Timing Slice
  if (ARSliceType == 0) begin : gen_ar_slice_forward
    br_flow_reg_fwd #(
        .Width(
        AddrWidth +
        IdWidth +
        br_amba::AxiBurstLenWidth +
        br_amba::AxiBurstSizeWidth +
        br_amba::AxiBurstTypeWidth +
        br_amba::AxiProtWidth +
        ARUserWidth
      )
    ) br_flow_reg_fwd_ar_slice (
        .clk,
        .rst,
        .push_ready(target_arready),
        .push_valid(target_arvalid),
        .push_data({
          target_araddr,
          target_arid,
          target_arlen,
          target_arsize,
          target_arburst,
          target_arprot,
          target_aruser
        }),
        .pop_ready(init_arready),
        .pop_valid(init_arvalid),
        .pop_data({
          init_araddr, init_arid, init_arlen, init_arsize, init_arburst, init_arprot, init_aruser
        })
    );
  end : gen_ar_slice_forward

  if (ARSliceType == 1) begin : gen_ar_slice_reverse
    br_flow_reg_rev #(
        .Width(
        AddrWidth +
        IdWidth +
        br_amba::AxiBurstLenWidth +
        br_amba::AxiBurstSizeWidth +
        br_amba::AxiBurstTypeWidth +
        br_amba::AxiProtWidth +
        ARUserWidth
      )
    ) br_flow_reg_rev_ar_slice (
        .clk,
        .rst,
        .push_ready(target_arready),
        .push_valid(target_arvalid),
        .push_data({
          target_araddr,
          target_arid,
          target_arlen,
          target_arsize,
          target_arburst,
          target_arprot,
          target_aruser
        }),
        .pop_ready(init_arready),
        .pop_valid(init_arvalid),
        .pop_data({
          init_araddr, init_arid, init_arlen, init_arsize, init_arburst, init_arprot, init_aruser
        })
    );
  end : gen_ar_slice_reverse

  if (ARSliceType == 2) begin : gen_ar_slice_full
    br_flow_reg_both #(
        .Width(
        AddrWidth +
        IdWidth +
        br_amba::AxiBurstLenWidth +
        br_amba::AxiBurstSizeWidth +
        br_amba::AxiBurstTypeWidth +
        br_amba::AxiProtWidth +
        ARUserWidth
      )
    ) br_flow_reg_both_ar_slice (
        .clk,
        .rst,
        .push_ready(target_arready),
        .push_valid(target_arvalid),
        .push_data({
          target_araddr,
          target_arid,
          target_arlen,
          target_arsize,
          target_arburst,
          target_arprot,
          target_aruser
        }),
        .pop_ready(init_arready),
        .pop_valid(init_arvalid),
        .pop_data({
          init_araddr, init_arid, init_arlen, init_arsize, init_arburst, init_arprot, init_aruser
        })
    );
  end : gen_ar_slice_full

  if (RSliceType == 0) begin : gen_r_slice_forward
    br_flow_reg_fwd #(
        .Width(IdWidth + DataWidth + br_amba::AxiRespWidth + RUserWidth + br_amba::AxiRLastWidth)
    ) br_flow_reg_fwd_r_slice (
        .clk,
        .rst,
        .push_ready(init_rready),
        .push_valid(init_rvalid),
        .push_data ({init_rid, init_rdata, init_rresp, init_ruser, init_rlast}),
        .pop_ready (target_rready),
        .pop_valid (target_rvalid),
        .pop_data  ({target_rid, target_rdata, target_rresp, target_ruser, target_rlast})
    );
  end : gen_r_slice_forward

  if (RSliceType == 1) begin : gen_r_slice_reverse
    br_flow_reg_rev #(
        .Width(IdWidth + DataWidth + br_amba::AxiRespWidth + RUserWidth + br_amba::AxiRLastWidth)
    ) br_flow_reg_rev_r_slice (
        .clk,
        .rst,
        .push_ready(init_rready),
        .push_valid(init_rvalid),
        .push_data ({init_rid, init_rdata, init_rresp, init_ruser, init_rlast}),
        .pop_ready (target_rready),
        .pop_valid (target_rvalid),
        .pop_data  ({target_rid, target_rdata, target_rresp, target_ruser, target_rlast})
    );
  end : gen_r_slice_reverse

  if (RSliceType == 2) begin : gen_r_slice_full
    br_flow_reg_both #(
        .Width(IdWidth + DataWidth + br_amba::AxiRespWidth + RUserWidth + br_amba::AxiRLastWidth)
    ) br_flow_reg_both_r_slice (
        .clk,
        .rst,
        .push_ready(init_rready),
        .push_valid(init_rvalid),
        .push_data ({init_rid, init_rdata, init_rresp, init_ruser, init_rlast}),
        .pop_ready (target_rready),
        .pop_valid (target_rvalid),
        .pop_data  ({target_rid, target_rdata, target_rresp, target_ruser, target_rlast})
    );
  end : gen_r_slice_full

endmodule : br_amba_axi_timing_slice
