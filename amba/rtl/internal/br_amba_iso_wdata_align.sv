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

// Bedrock-RTL AMBA WDATA Align and Hold
//
// This module is used in the context of an AXI isolator that disconnects
// a downstream AXI subordinate from an upstream AXI manager. This
// module is used to track the relative skew between the AW and W
// channels, and then to force it into alignment (by holding off either
// channel until they are aligned) and then finally holding off the
// upstream entirely.
//
// Alignment is initiated by asserting align_and_hold_req. This signal
// must be kept asserted until align_and_hold_done is asserted,
// indicating that the alignment is complete and no new requests will be
// accepted on either W or AW. Upstream ports will then remain
// backpressured until align_and_hold_req is deasserted.
//
// Recovering alignment is necessary prior to reconnecting the downstream
// subordinate to the upstream manager after the subordinate has been
// disconnected for some time. After the reconnect is made, the hold is
// released, and transactions are allowed to flow to the downstream
// subordinate again.
//
// The module is parameterized by the maximum skew between the AW and W
// channels (MaxTransactionSkew) measured in number of maximum size
// (MaxAxiBurstLen) transactions.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_amba_iso_wdata_align #(
    // Maximum allowed skew (measured in max-length transactions) that can be tracked
    // without causing backpressure on the upstream ports.
    parameter int MaxTransactionSkew = 2,
    // can be set to 1 for AXI-Lite, otherwise should be set to br_amba::AxiBurstLenWidth
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    parameter int AxiBurstLenWidth = br_math::clamped_clog2(MaxAxiBurstLen),
    // If set to 1, then the module will block pushes on the upstream W channel if it would
    // result in excess data beats (i.e. data will never be forwarded unless it is associated with
    // an AW request that has been forwarded previously or on the same cycle).
    parameter bit PreventExcessData = 0,
    // If set to 1, then the module will block pushes on the upstream W channel and insert fake
    // write data on the downstream W channel until the alignment is complete. To be used in the
    // case where the upstream side is going to be reset and we don't want to rely on the upstream
    // to quiesce the interface properly.
    parameter bit FakeWriteDataOnAlign = 0
) (
    input logic clk,
    input logic rst,
    //
    output logic upstream_awready,
    input logic upstream_awvalid,
    input logic [AxiBurstLenWidth-1:0] upstream_awlen,
    //
    output logic upstream_wready,
    input logic upstream_wvalid,
    //
    input logic downstream_awready,
    output logic downstream_awvalid,
    //
    input logic downstream_wready,
    output logic downstream_wvalid,
    //
    input logic align_and_hold_req,
    output logic align_and_hold_done
);

  // Integration checks
  `BR_ASSERT_STATIC(max_transaction_skew_gte_1_a, MaxTransactionSkew > 1)
  `BR_ASSERT_STATIC(max_axi_burst_len_1_or_amba_a,
                    MaxAxiBurstLen == 1 || MaxAxiBurstLen == 2 ** br_amba::AxiBurstLenWidth)
  `BR_ASSERT_INTG(legal_request_rise_a, $rose(align_and_hold_req) |-> !$past(align_and_hold_done))
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(align_and_hold_req) |-> $past(align_and_hold_done))
  `BR_ASSERT_INTG(awlen_legal_range_a, upstream_awvalid |-> upstream_awlen < MaxAxiBurstLen)

  // FakeWriteDataOnAlign requires PreventExcessData to be set to 1
  `BR_ASSERT_STATIC(fake_write_data_on_align_req_a, PreventExcessData || !FakeWriteDataOnAlign)

  localparam int MaxBurstLenWidth = $clog2(MaxAxiBurstLen + 1);
  localparam int MaxExcessCount = MaxTransactionSkew * MaxAxiBurstLen;
  localparam int MaxExcessCountWidth = $clog2(MaxExcessCount + 1);

  logic [MaxExcessCountWidth-1:0] excess_w_data_beats;
  logic [MaxExcessCountWidth-1:0] excess_aw_data_beats;
  logic aw_beat, w_beat;
  logic [MaxBurstLenWidth-1:0] aw_beat_len;
  logic excess_w_full, excess_aw_full;
  logic [MaxBurstLenWidth-1:0] excess_aw_incr, excess_aw_decr;
  logic [MaxBurstLenWidth-1:0] excess_w_incr, excess_w_decr;
  logic excess_aw_incr_valid, excess_aw_decr_valid;
  logic excess_w_incr_valid, excess_w_decr_valid;
  logic w_beats_in_excess;
  logic aw_beats_in_excess;
  logic aw_and_w_beats_aligned;
  logic holdoff_aw;
  logic holdoff_w;
  logic block_upstream_and_fake_w;

  // AWLEN is 0 based, so we need to add 1 to get the actual number of beats
  if (MaxAxiBurstLen == 1) begin : gen_aw_len_single_beat
    assign aw_beat_len = 1'b1;
    `BR_UNUSED(upstream_awlen)
  end else begin : gen_aw_len_multi_beat
    assign aw_beat_len = upstream_awlen + 1'b1;
  end

  // Counters track all upstream beats (regardless of what happens on downstream)
  assign aw_beat = upstream_awvalid && upstream_awready;
  assign w_beat  = (upstream_wvalid || block_upstream_and_fake_w) && upstream_wready;

  //
  // Excess AW data beat counter. Indicates how many excess WDATA beats implied
  // by the previously accepted AW requests in excess of the number of WDATA beats
  // received (i.e. how many additional WDATA beats are expected).
  //

  br_counter #(
      .MaxValue(MaxExcessCount),
      .MaxChange(MaxAxiBurstLen),
      .EnableWrap(0),
      .EnableSaturate(0)
  ) br_counter_excess_aw (
      .clk(clk),
      .rst(rst),
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(excess_aw_incr_valid),
      .incr(excess_aw_incr),
      .decr_valid(excess_aw_decr_valid),
      .decr(excess_aw_decr),
      .value(excess_aw_data_beats),
      .value_next()
  );

  // Increment by the number of beats in the newly-accepted request, minus any excess
  // data beats the new transaction consumes
  // ri lint_check_waive LHS_TOO_SHORT ARITH_BITLEN
  assign excess_aw_incr = aw_beat_len - excess_w_data_beats;
  // ri lint_check_waive ARITH_BITLEN
  assign excess_aw_incr_valid = aw_beat && (excess_w_data_beats <= aw_beat_len);

  // Decrement by 1 for each newly-arriving data beat, if we have excess data beats
  // to consume
  assign excess_aw_decr = 1'b1;
  assign excess_aw_decr_valid = w_beat && (excess_aw_data_beats > 0);

  // When there is not enough counter space to hold an additional (max AWLEN) AW request,
  // then we need to assert the excess_aw_full signal
  assign excess_aw_full = (excess_aw_data_beats >= (MaxExcessCount - MaxAxiBurstLen));

  //
  // Excess W data beat counter. Indicates how many WDATA beats we have received
  // in excess of the number of beats expected from all of the previously accepted
  // AW requests (i.e. how many additional WDATA beats are expected to be requested
  //in future AW requests).
  //

  br_counter #(
      .MaxValue(MaxExcessCount),
      .MaxChange(MaxAxiBurstLen),
      .EnableWrap(0),
      .EnableSaturate(0)
  ) br_counter_excess_w (
      .clk(clk),
      .rst(rst),
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(excess_w_incr_valid),
      .incr(excess_w_incr),
      .decr_valid(excess_w_decr_valid),
      .decr(excess_w_decr),
      .value(excess_w_data_beats),
      .value_next()
  );

  // Increment by 1 if there is no excess AW data beats to consume
  assign excess_w_incr = 1'b1;
  assign excess_w_incr_valid = w_beat && (excess_aw_data_beats == 0);

  // Decrement by the number of beats in the newly-accepted request or the
  // amount of excess w beats available to consume, whichever is smaller
  // ri lint_check_waive LHS_TOO_SHORT ARITH_BITLEN COND_OP_BITLEN
  assign excess_w_decr = (aw_beat_len <= excess_w_data_beats) ? aw_beat_len : excess_w_data_beats;
  assign excess_w_decr_valid = aw_beat && (excess_w_data_beats > 0);

  // When there is not enough counter space to hold an additional WDATA beat,
  // then we need to assert the excess_w_full signal
  assign excess_w_full = (excess_w_data_beats >= (MaxExcessCount - 1));

  //
  // Decision logic
  //

  assign aw_beats_in_excess = (excess_aw_data_beats > excess_w_data_beats);
  assign w_beats_in_excess = (excess_w_data_beats > excess_aw_data_beats);
  assign aw_and_w_beats_aligned = (excess_aw_data_beats == '0 && excess_w_data_beats == '0);

  // Hold off upstream->downstream transfer if the counter space is exhausted (one of the ports is
  // too far ahead of the other) or an operation is underway force alignment and one of the upstream
  // ports is ahead (in excess) of the other or if the alignment is complete.
  if (PreventExcessData) begin : gen_prevent_excess_data
    assign holdoff_w = excess_w_full
                        || (align_and_hold_req && w_beats_in_excess)
                        || align_and_hold_done
        // hold off if the data doesn't have an associated AW request
        || !(aw_beats_in_excess || (downstream_awready && upstream_awvalid));
  end else begin : gen_allow_excess_data
    assign holdoff_w = excess_w_full
                        || (align_and_hold_req && w_beats_in_excess)
                        || align_and_hold_done;
  end

  assign holdoff_aw = excess_aw_full
                        || (align_and_hold_req && aw_beats_in_excess)
                        || align_and_hold_done;

  // If FakeWriteDataOnAlign is set, then we need to block upstream W channel pushes and
  // insert fake write data on the downstream W channel until the alignment is complete.
  //
  // When FakeWriteDataOnAlign is not set, we rely on the upstream AXI manager to
  // supply valid W and AW streams to eventually bring things into alignment.
  if (FakeWriteDataOnAlign) begin : gen_fake_write_data
    assign block_upstream_and_fake_w = align_and_hold_req;
  end else begin : gen_no_fake_write_data
    assign block_upstream_and_fake_w = 1'b0;
  end

  // Assign upstream->downstream ready/valid handshake signals.
  assign upstream_awready = downstream_awready && !holdoff_aw && !block_upstream_and_fake_w;
  assign upstream_wready = downstream_wready && !holdoff_w && !block_upstream_and_fake_w;
  assign downstream_awvalid = upstream_awvalid && !holdoff_aw;
  assign downstream_wvalid = (upstream_wvalid || block_upstream_and_fake_w) && !holdoff_w;

  assign align_and_hold_done = align_and_hold_req && aw_and_w_beats_aligned;

  //
  // Assertions
  //

  // verilog_format: off
  `BR_ASSERT(if_counts_eq_then_zero_a, (excess_aw_data_beats == excess_w_data_beats)
        |-> (excess_aw_data_beats == '0 && excess_w_data_beats == '0))
  // verilog_format: on
endmodule
