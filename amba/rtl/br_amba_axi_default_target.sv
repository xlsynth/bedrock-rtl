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

// AXI4 Default Target
//
// This module acts as an AXI4 default target.
//
// The DecodeError and SlvErr parameters determine the response that the target
// will return. If DecodeError is 1, the target will respond with a DECERR
// response. If SlvErr is 1, the target will respond with a SLVERR response.
// If both DecodeError and SlvErr are 0, the target will respond with an OKAY
// response.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_amba_axi_default_target #(
    parameter int DataWidth = 64,
    parameter bit DecodeError = 1,
    parameter bit SlvErr = 0,
    parameter int AxiIdWidth = 1,
    parameter bit SingleBeat = 0,
    parameter logic [DataWidth-1:0] DefaultReadData = '0,
    localparam int AxiLenWidth = SingleBeat ? 1 : br_amba::AxiBurstLenWidth
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Reduced AXI4-Lite target interface
    input  logic                             target_awvalid,
    output logic                             target_awready,
    input  logic [           AxiIdWidth-1:0] target_awid,
    input  logic [          AxiLenWidth-1:0] target_awlen,
    input  logic                             target_wvalid,
    output logic                             target_wready,
    input  logic                             target_wlast,
    output logic                             target_bvalid,
    input  logic                             target_bready,
    output logic [           AxiIdWidth-1:0] target_bid,
    output logic [br_amba::AxiRespWidth-1:0] target_bresp,
    input  logic                             target_arvalid,
    output logic                             target_arready,
    input  logic [           AxiIdWidth-1:0] target_arid,
    input  logic [          AxiLenWidth-1:0] target_arlen,
    output logic                             target_rvalid,
    input  logic                             target_rready,
    output logic [            DataWidth-1:0] target_rdata,
    output logic [br_amba::AxiRespWidth-1:0] target_rresp,
    output logic [           AxiIdWidth-1:0] target_rid,
    output logic                             target_rlast
);

  // Integration checks
  `BR_ASSERT_STATIC(one_resp_only_a, !(DecodeError && SlvErr))

  if (SingleBeat) begin : gen_single_beat_asserts
    `BR_ASSERT_INTG(single_beat_arlen_a, target_arvalid |-> target_arlen == 1'b0)
    `BR_ASSERT_INTG(single_beat_awlen_a, target_awvalid |-> target_awlen == 1'b0)
    `BR_ASSERT_INTG(single_beat_wlast_a, target_wvalid |-> target_wlast == 1'b1)
  end

  // Internal signals
  logic awfifo_pop_valid, awfifo_pop_ready;
  logic [AxiIdWidth-1:0] awfifo_pop_awid;
  logic wfifo_pop_valid, wfifo_pop_ready;
  logic arfifo_pop_valid, arfifo_pop_ready;
  logic [ AxiIdWidth-1:0] arfifo_pop_arid;
  logic [AxiLenWidth-1:0] arfifo_pop_arlen;

  // Response signals
  if (DecodeError) begin : gen_decode_error
    assign target_bresp = br_amba::AxiRespDecerr;  // ri lint_check_waive ENUM_RHS
    assign target_rresp = br_amba::AxiRespDecerr;  // ri lint_check_waive ENUM_RHS
  end else if (SlvErr) begin : gen_slv_err
    assign target_bresp = br_amba::AxiRespSlverr;  // ri lint_check_waive ENUM_RHS
    assign target_rresp = br_amba::AxiRespSlverr;  // ri lint_check_waive ENUM_RHS
  end else begin : gen_okay
    assign target_bresp = br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_RHS
    assign target_rresp = br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_RHS
  end

  assign target_rdata = DefaultReadData;

  // Write address channel
  br_flow_reg_fwd #(
      .Width(AxiIdWidth)
  ) br_flow_reg_fwd_aw (
      .clk,
      .rst,

      .push_ready(target_awready),
      .push_valid(target_awvalid),
      .push_data (target_awid),

      .pop_ready(awfifo_pop_ready),
      .pop_valid(awfifo_pop_valid),
      .pop_data (awfifo_pop_awid)
  );
  `BR_UNUSED(target_awlen)

  // Only pop from write address channel when write response is ready and valid
  assign awfifo_pop_ready = target_bready && target_bvalid;

  // Write data channel
  br_flow_reg_fwd #(
      .Width(1)
  ) br_flow_reg_fwd_w (
      .clk,
      .rst,

      .push_ready(target_wready),
      .push_valid(target_wvalid && target_wlast),
      .push_data (1'b0),

      .pop_ready(wfifo_pop_ready),
      .pop_valid(wfifo_pop_valid),
      .pop_data ()
  );

  // Only pop from write data channel when write response is ready and valid
  assign wfifo_pop_ready = target_bready && target_bvalid;

  // Generate write response when both address and data channels have valid signals
  assign target_bvalid   = awfifo_pop_valid && wfifo_pop_valid;
  assign target_bid      = awfifo_pop_awid;

  // Read address and response channels
  br_flow_reg_fwd #(
      .Width(AxiIdWidth + AxiLenWidth)
  ) br_flow_reg_fwd_ar (
      .clk,
      .rst,

      .push_ready(target_arready),
      .push_valid(target_arvalid),
      .push_data ({target_arid, target_arlen}),

      .pop_ready(arfifo_pop_ready),
      .pop_valid(arfifo_pop_valid),
      .pop_data ({arfifo_pop_arid, arfifo_pop_arlen})
  );

  if (SingleBeat) begin : gen_single_beat
    assign arfifo_pop_ready = target_rready;
    assign target_rvalid    = arfifo_pop_valid;
    assign target_rid       = arfifo_pop_arid;
    assign target_rlast     = 1'b1;
    `BR_UNUSED(arfifo_pop_arlen)
  end else begin : gen_multi_beat
    logic rbeat;
    logic last;
    logic reinit;
    logic [AxiLenWidth-1:0] beat_count;

    assign rbeat  = target_rready && target_rvalid;
    assign last   = (beat_count == arfifo_pop_arlen);
    assign reinit = last && rbeat;
    br_counter_incr #(
        .MaxValue(2 ** AxiLenWidth - 1),
        .MaxIncrement(1),
        .EnableReinitAndIncr(0),
        .EnableSaturate(0)
    ) br_counter_incr_arlen (
        .clk,
        .rst,
        //
        .reinit(reinit),
        .initial_value('0),
        .incr_valid(rbeat),
        .incr(1'b1),
        .value(beat_count),
        .value_next()
    );

    assign target_rvalid = arfifo_pop_valid;
    assign target_rid    = arfifo_pop_arid;
    assign target_rlast  = last;
    assign arfifo_pop_ready = target_rready && last;
  end

endmodule : br_amba_axi_default_target
