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

// Bedrock-RTL Flow Deserializer
//
// This module deserializes packet flits from a narrow bus onto a wider bus.
// Data flows from push-side to pop-side using ready-valid handshakes on both sides.
//
// The push and pop bitwidths are parameterized; the PopWidth must be a positive integer
// that is greater than PushWidth and is also divisible by PushWidth.
// The flit deserialization ratio is given by DeserializationRatio = PopWidth / PushWidth, i.e.,
// the ratio of bus widths is DeserializationRatio:1 for some integer DeserializationRatio >= 1 and the
// maximum number of push flits per pop flit is DeserializationRatio.
//
// When DeserializationRatio is 1, then this module is a pass-through.
//
// The deserialization order is configured by DeserializeMostSignificantFirst. If 1, then the most-significant
// bits of the pop flit are reconstructed first from incoming push flits; otherwise, the least-significant bits
// are reconstructed first. The order of bits within each reconstructed pop flit matches the concatenation order
// of the individual push flits.
//
// Each pop flit is accompanied by a pop_metadata sideband signal that is formed by sampling the push_metadata
// associated with the set of push flits that compose that pop flit. The module does not care about the contents
// of push_metadata. The push_metadata is required to be constant across every push flit in matching the same pop flit,
// and so the deserializer samples it only on the last push flit of the packet.
//
// The push interface has a push_last signal that indicates the last flit of a packet on the push side.
// Up to DeserializationRatio push flits combine to form one pop flit. The pop flit is greedily constructed
// until either the pop flit is full (DeserializationRatio push flits have been consumed) or push_last is 1.
// When push_last is 1, then the number of push flits that were consumed to form the last pop flit can vary between 1
// and DeserializationRatio.
//
// The pop interface sets pop_last to 1 when the packet deserialization is complete (as indicated by push_last).
// If the total number of push flits in the packet is not divisible by DeserializationRatio (i.e., push_last comes
// "early"), then the last pop flit is partially populated and the remaining space is filled with zeros.
// If DeserializeMostSignificantFirst is 1, then the zero-filled values occupy the least-significant portion of
// the final pop flit; otherwise, they occupy the most-significant portion.
//
// The pop_last_dont_care_count port indicates how much of the last pop_data flit contains "don't care"
// values. The don't care values are always in contiguous multiples of PopWidth bits. If DeserializeMostSignificantFirst is 1,
// then the don't care values are the least-significant bits; otherwise, they are the most-significant bits, i.e., either way,
// the tail end of the flit.
//
// The push_valid, push_data, push_last, and push_metadata must be held stable until push_ready is 1.
//
// The throughput of this module is 1 pop flit per DeserializationRatio cycles; equivalently, a packet initiation interval of
// 1 packet per DeserializationRatio cycles. The throughput can increase if push_last is used to send packets that are
// not evenly divisible by DeserializationRatio, because the push-side stream is compressed.
//
// The latency from the first push flit valid to the pop flit being valid varies from 0 cycles (when push_last is 1 on the first flit)
// up to (DeserializationRatio - 1) cycles (when push_last is 1 on the last flit or not set at all).
//
// The implementation uses a demux into staging registers rather than a shift register to reduce power.
//
// Examples (where the ready signals are not shown and are assumed to always be 1; X denotes an unknown value when pop_valid is 0):
//
//     Packet length = 32 bits (4 push flits), not using last bit
//     PushWidth = 8, PopWidth = 32, MetadataWidth = 3, (DeserializationRatio = 4), DeserializeMostSignificantFirst = 1
//     Cycle | push_valid | push_data | push_last | push_metadata | pop_valid | pop_data     | pop_last | pop_last_dont_care_count | pop_metadata
//     ------|------------|-----------|-----------|---------------|-----------|--------------|----------|--------------------------|-------------
//     0     | 1'b1       | 8'hBA     | 1'b0      | 3'd6          | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     1     | 1'b1       | 8'hAD     | 1'b0      | stable        | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     2     | 1'b1       | 8'hF0     | 1'b0      | stable        | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     3     | 1'b1       | 8'h0D     | 1'b0      | stable        | 1'b1      | 32'hBAADF00D | 1'b0     | 2'd0                     | 3'd6
//
//     Packet length = 56 bits (7 push flits), using last bit
//     PushWidth = 8, PopWidth = 32, MetadataWidth = 3, (DeserializationRatio = 4), DeserializeMostSignificantFirst = 0
//     Cycle | push_valid | push_data | push_last | push_metadata | pop_valid | pop_data     | pop_last | pop_last_dont_care_count | pop_metadata
//     ------|------------|-----------|-----------|---------------|-----------|--------------|----------|--------------------------|-------------
//     0     | 1'b1       | 8'h67     | 1'b0      | 3'd2          | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     1     | 1'b1       | 8'h45     | 1'b0      | stable        | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     2     | 1'b1       | 8'h23     | 1'b0      | stable        | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     3     | 1'b1       | 8'h01     | 1'b0      | stable        | 1'b1      | 32'h01234567 | 1'b0     | 2'd0                     | 3'd2
//     4     | 1'b1       | 8'h0D     | 1'b0      | 3'd5          | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     5     | 1'b1       | 8'hF0     | 1'b0      | stable        | 1'b0      | 32'hXXXXXXXX | 1'bX     | 2'd0                     | 3'dX
//     6     | 1'b1       | 8'hAD     | 1'b1      | stable        | 1'b1      | 32'hXXADF00D | 1'b1     | 2'd1                     | 3'd5

`include "br_asserts.svh"
`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_tieoff.svh"

module br_flow_deserializer #(
    // Width of the push side flit. Must be at least 1.
    parameter int PushWidth = 1,
    // Width of the pop side packet. Must be greater than PushWidth
    // and evenly divisible by PushWidth.
    parameter int PopWidth = 2,
    // Width of the sideband metadata (not serialized). Must be at least 1.
    parameter int MetadataWidth = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, the most significant bits of the packet are received first (big endian).
    // If 0, the least significant bits are received first (little endian).
    // The order of bits within each flit is always the same that they
    // appear on the push interface.
    parameter bit DeserializeMostSignificantFirst = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int DeserializationRatio = PopWidth / PushWidth,
    // Vector widths cannot be 0, so we need to special-case when DeserializationRatio == 1
    // even though the pop_last_dont_care_count port will be unused downstream in that case.
    localparam int SerFlitIdWidth = DeserializationRatio > 1 ? $clog2(DeserializationRatio) : 1
) (
    // Posedge-triggered clock
    input logic clk,
    // Synchronous active-high reset
    input logic rst,

    // Push-side interface (narrow, serialized flits).
    output logic                     push_ready,
    input  logic                     push_valid,
    input  logic [    PushWidth-1:0] push_data,
    // Indicates the last push flit in the packet. Safe to tie to 0
    // if you don't need to keep track of this in external logic.
    input  logic                     push_last,
    // Constant packet metadata carried alongside each push flit;
    // passed directly to the pop interface.
    input  logic [MetadataWidth-1:0] push_metadata,

    // Pop-side interface (wide flits).
    input  logic                      pop_ready,
    output logic                      pop_valid,
    // If pop_last is 1, inspect pop_last_dont_care_count to determine
    // how much of the pop_data consists of valid data.
    output logic [      PopWidth-1:0] pop_data,
    // Indicates that this is the last pop flit of a packet.
    output logic                      pop_last,
    // This signal should only be used when push_last is 1.
    // (If push_last is 0, then it's driven to 0.)
    // When push_last is 1, then this is the
    // number of don't care slices at the tail end of the pop flit.
    // It is less than DeserializationRatio, i.e., the entire pop flit
    // will not consist of "don't care" slices. 0 means the pop flit
    // is entirely populated with valid data.
    output logic [SerFlitIdWidth-1:0] pop_last_dont_care_count,
    output logic [ MetadataWidth-1:0] pop_metadata
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(push_width_gte_1_a, PushWidth >= 1)
  `BR_ASSERT_STATIC(pop_width_multiple_of_push_width_a, (PopWidth % PushWidth) == 0)
  `BR_ASSERT_STATIC(metadata_width_gte_1_a, MetadataWidth >= 1)
  `BR_ASSERT_STATIC(deserialization_ratio_gte_1_a, DeserializationRatio >= 1)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(PushWidth + 1 + MetadataWidth),
      // Push ready/valid stability is required for the deserializer to work correctly.
      // That's because it serially receives the valid push data until the entire packet
      // has been received. If the push data is unstable during reception, then the data
      // integrity is compromised.
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableCoverPushBackpressure),
      .EnableAssertDataStability(EnableCoverPushBackpressure),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({push_data, push_last, push_metadata})
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Base case: pass-through.
  if (DeserializationRatio == 1) begin : gen_dr_eq_1
    assign pop_valid = push_valid;
    assign pop_data  = push_data;
    assign pop_last  = push_last;
    // ri lint_check_waive CONST_OUTPUT
    `BR_TIEOFF_ZERO(pop_last_dont_care_count)
    assign pop_metadata = push_metadata;
    assign push_ready   = pop_ready;

    // General case: deserialize.
  end else begin : gen_dr_gt_1

    //------
    // FSM is just an incrementing counter that keeps track of the push flit ID.
    // When push_last is 0, then this simply counts up to the DeserializationRatio - 1
    // and then we complete the pop flit. When push_last is 1, then we can complete
    // the pop flit early.
    //
    // Reinitialize the counter on the cycle that the pop flit is completed so that a new pop flit
    // can be started on the next cycle.
    //------
    localparam int DrMinus1 = DeserializationRatio - 1;

    logic                      push_flit_id_incr_valid;
    logic [SerFlitIdWidth-1:0] push_flit_id;
    logic                      push;
    logic                      pop;

    br_counter_incr #(
        .MaxValue(DrMinus1),
        .MaxIncrement(1),
        .EnableWrap(0),
        .EnableCoverZeroIncrement(0),
        .EnableCoverReinitAndIncr(0),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_counter_incr_push_flit_id (
        .clk,
        .rst,
        .reinit(pop),
        .initial_value(SerFlitIdWidth'(0)),
        .incr_valid(push_flit_id_incr_valid),
        .incr(1'b1),
        .value(push_flit_id),
        .value_next()  // unused
    );

    assign push = push_ready && push_valid;
    assign pop = pop_ready && pop_valid;
    assign push_flit_id_incr_valid = !pop && push;

    //-----
    // Use the push_flit_id to demux the incoming push_data into slices that form the pop_data.
    //-----
    logic [DeserializationRatio-1:0] slice_valid;
    logic [DeserializationRatio-1:0][PushWidth-1:0] slice_data;

    br_demux_bin #(
        .NumSymbolsOut(DeserializationRatio),
        .SymbolWidth(PushWidth),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_demux_bin (
        .select(push_flit_id),
        .in_valid(push_valid),
        .in(push_data),
        .out_valid(slice_valid),
        .out(slice_data)
    );

    //-----
    // Register the slice data for all but the last slice.
    //-----
    logic [SerFlitIdWidth-1:0] dr_minus_1;
    logic [DeserializationRatio-2:0][PushWidth-1:0] slice_reg;
    logic [DeserializationRatio-2:0] slice_reg_ld_en;

    assign dr_minus_1 = DrMinus1;

    for (genvar i = 0; i < DrMinus1; i++) begin : gen_reg
      `BR_REGL(slice_reg[i], slice_data[i], slice_reg_ld_en[i])
      assign slice_reg_ld_en[i] = slice_valid[i] && push && !push_last;
    end

    //-----
    // Concat & merge the pop interface; all deserialized flits must be synchronously popped.
    //-----
    for (genvar i = 0; i < DeserializationRatio; i++) begin : gen_pop_data_concat
      localparam int Lsb =
        DeserializeMostSignificantFirst ?
        ((DeserializationRatio - i) - 1) * PushWidth :
        i * PushWidth;
      localparam int Msb = Lsb + PushWidth - 1;

      if (i < DrMinus1) begin : gen_mux
        logic passthru_this_slice;
        assign passthru_this_slice = push_last && (push_flit_id == i);

        br_mux_bin #(
            .NumSymbolsIn(2),
            .SymbolWidth (PushWidth)
        ) br_mux_bin (
            .select(passthru_this_slice),
            .in({slice_data[i], slice_reg[i]}),
            .out(pop_data[Msb:Lsb]),
            .out_valid()
        );

        // Last slice does not have a register to mux from.
      end else begin : gen_no_mux
        assign pop_data[Msb:Lsb] = slice_data[i];
      end
    end

    //------
    // Drive the rest of the pop interface outputs.
    // The metadata is sampled from the last push flit.
    //------
    assign pop_valid = slice_valid[DrMinus1] || (push_valid && push_last);
    assign pop_last = push_last;
    assign pop_last_dont_care_count = pop_last ? (dr_minus_1 - push_flit_id) : 0;
    assign pop_metadata = push_metadata;

    //------
    // Complete the push flit when we're completing the pop flit or when we
    // we're not done building up the pop flit in registers.
    //------
    logic completing_pop_flit;
    logic not_done_building_pop_flit;

    assign completing_pop_flit = pop_ready && (pop_last || (push_flit_id == dr_minus_1));
    assign not_done_building_pop_flit = !(push_valid && push_last) && (push_flit_id < dr_minus_1);
    assign push_ready = completing_pop_flit || not_done_building_pop_flit;

    `BR_ASSERT_IMPL(
        incomplete_pop_flit_a,
        pop_valid && (push_flit_id < dr_minus_1) |-> pop_last && pop_last_dont_care_count != 0)

  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(PopWidth + 1 + SerFlitIdWidth + MetadataWidth),
      // Pop ready/valid stability can only be guaranteed if the push side is also stable.
      // We already check that above, so here we just unconditionally check the implementation.
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data ({pop_data, pop_last, pop_last_dont_care_count, pop_metadata})
  );

  `BR_ASSERT_IMPL(pop_valid_iff_last_a, pop_valid |-> push_valid)
  `BR_ASSERT_IMPL(pop_last_iff_push_last_a, pop_valid && pop_last |-> push_last)
  `BR_ASSERT_IMPL(complete_pop_flit_no_last_a,
                  pop_valid && !pop_last |-> pop_last_dont_care_count == 0)

endmodule : br_flow_deserializer
