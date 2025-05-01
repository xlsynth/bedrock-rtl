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

// Bedrock-RTL Flow Serializer
//
// This module serializes packet flits from a wide bus onto a narrow bus.
// Data flows from push-side to pop-side using ready-valid handshakes on both sides.
//
// The push and pop bitwidths are parameterized; the PushWidth must be a positive integer
// that is greater than PopWidth and is also divisible by PopWidth.
// The flit serialization ratio is given by SerializationRatio = PushWidth / PopWidth, i.e.,
// the ratio of bus widths is 1:SerializationRatio for some integer SerializationRatio >= 1 and the
// maximum number of pop flits per push flit is SerializationRatio.
//
// When SerializationRatio is 1, then this module is a pass-through.
//
// The serialization order is configured by SerializeMostSignificantFirst. If 1, then the most-significant
// bits of the push flit are sent first; otherwise, the least-significant are sent first.
// The order of bits within each pop flit is always the same that they appear in a slice of the push flit.
//
// Each push flit is accompanied by a push_metadata sideband signal that does not get serialized.
// It is replicated on the pop side as pop_metadata for each pop flit corresponding to the same push flit.
// The module does not care about the contents of push_metadata.
//
// The push interface has a push_last signal that indicates the last flit of a packet on the push side.
// For push flits where push_last is 0, then exactly SerializationRatio pop flits are produced.
// When push_last is 1, then the number of pop flits produced can vary between 1 and SerializationRatio. The exact
// number is given by (SerializationRatio - push_last_dont_care_count).
//
// The push_last_dont_care_count port indicates how much of the last push_data flit contains "don't care"
// values that can be dropped from the serialized transmission. The don't care values are always in contiguous
// multiples of PopWidth bits. If SerializeMostSignificantFirst is 1, then the don't care values are the
// least-significant bits; otherwise, they are the most-significant bits, i.e., either way, the tail end of the flit.
//
// The push_valid, push_data, push_last, push_last_dont_care_count, and push_metadata must be held stable until push_ready is 1.
//
// The throughput of this module is 1 pop flit per cycle; equivalently, a packet initiation interval of
// 1 packet per SerializationRatio cycles. The throughput can increase if push_last and push_last_dont_care_count are used
// to send packets that are not evenly divisible by SerializationRatio, allowing the pop-side stream to be compressed.
//
// The cut-through latency of the push packet to the first pop flit is 0 cycles.
//
// The implementation uses a mux rather than a shift register to reduce power.
//
// Examples (where the ready signals are not shown and are assumed to always be 1; X denotes an unknown value):
//
//     Packet length = 32 bits (4 push flits), not using last bit
//     PushWidth = 32, PopWidth = 8, MetadataWidth = 3, (SerializationRatio = 4), SerializeMostSignificantFirst = 1
//     Cycle | push_valid | push_data    | push_last | push_last_dont_care_count | push_metadata | pop_valid | pop_data | pop_last | pop_metadata
//     ------|------------|--------------|-----------|---------------------------|---------------|-----------|----------|----------|------------
//     0     | 1'b1       | 32'hBAADF00D | 1'b0      | 2'd0                      | 3'd6          | 1'b1      | 8'hBA    | 1'b0     | 3'd6
//     1     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'hAD    | 1'b0     | 3'd6
//     2     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'hF0    | 1'b0     | 3'd6
//     3     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'h0D    | 1'b0     | 3'd6
//
//     Packet length = 56 bits (7 pop flits), using last bit
//     PushWidth = 32, PopWidth = 8, MetadataWidth = 3, (SerializationRatio = 4), SerializeMostSignificantFirst = 0
//     Cycle | push_valid | push_data    | push_last | push_last_dont_care_count | push_metadata | pop_valid | pop_data | pop_last | pop_metadata
//     ------|------------|--------------|-----------|---------------------------|---------------|-----------|----------|----------|------------
//     0     | 1'b1       | 32'h01234567 | 1'b0      | 2'd0                      | 3'd2          | 1'b1      | 8'h67    | 1'b0     | 3'd2
//     1     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'h45    | 1'b0     | 3'd2
//     2     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'h23    | 1'b0     | 3'd2
//     3     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'h01    | 1'b0     | 3'd2
//     4     | 1'b1       | 32'hXXADF00D | 1'b1      | 2'd1                      | 3'd5          | 1'b1      | 8'h0D    | 1'b0     | 3'd5
//     5     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'hF0    | 1'b0     | 3'd5
//     6     | stable     | stable       | stable    | stable                    | stable        | 1'b1      | 8'hAD    | 1'b1     | 3'd5

`include "br_asserts.svh"
`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_flow_serializer #(
    // Width of the push side packet. Must be greater than PopWidth
    // and evenly divisible by PopWidth.
    parameter int PushWidth = 2,
    // Width of the pop side flit. Must be at least 1.
    parameter int PopWidth = 1,
    // Width of the sideband metadata (not serialized). Must be at least 1.
    parameter int MetadataWidth = 1,
    // If 1, the most significant bits of the packet are sent first (big endian).
    // If 0, the least significant bits are sent first (little endian).
    // The order of bits within each flit is always the same that they
    // appear on the push interface.
    parameter bit SerializeMostSignificantFirst = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int SerializationRatio = PushWidth / PopWidth,
    // Vector widths cannot be 0, so we need to special-case when SerializationRatio == 1
    // even though the push_last_dont_care_count port won't be used in that case.
    localparam int SerFlitIdWidth = SerializationRatio > 1 ? $clog2(SerializationRatio) : 1
) (
    // Posedge-triggered clock
    input logic clk,
    // Synchronous active-high reset
    input logic rst,

    // Push-side interface (wide flits).
    output logic                      push_ready,
    input  logic                      push_valid,
    input  logic [     PushWidth-1:0] push_data,
    // Indicates that this is the last push flit of a packet.
    // Safe to tie to 0 if you don't need to keep track of this
    // in external logic.
    input  logic                      push_last,
    // If push_last is 1, then this is the number of don't care slices at
    // the tail end of the push flit. It must be less than SerializationRatio,
    // i.e., the entire push flit is not allowed to consist of "don't care" slices.
    // Drive to 0 if each push flit should be fully serialized and transmitted
    // over SerializationRatio pop flits. Must be 0 when push_last is 0.
    input  logic [SerFlitIdWidth-1:0] push_last_dont_care_count,
    // Constant metadata to carry alongside the flits.
    // Does not get serialized (simply replicated alongside each pop flit).
    input  logic [ MetadataWidth-1:0] push_metadata,

    // Pop-side interface (narrow, serialized flits).
    input  logic                     pop_ready,
    output logic                     pop_valid,
    output logic [     PopWidth-1:0] pop_data,
    // Driven to 1 on the last pop flit of the packet, i.e.,
    // the last slice of the push flit when push_last is 1.
    // If push_last is tied to 0 then pop_last will always be 0.
    output logic                     pop_last,
    // Each pop flit has replicated metadata from the push interface.
    output logic [MetadataWidth-1:0] pop_metadata
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(pop_width_gte_1_a, PopWidth >= 1)
  `BR_ASSERT_STATIC(push_width_multiple_of_pop_width_a, (PushWidth % PopWidth) == 0)
  `BR_ASSERT_STATIC(metadata_width_gte_1_a, MetadataWidth >= 1)
  `BR_ASSERT_STATIC(serialization_ratio_gte_1_a, SerializationRatio >= 1)

  `BR_ASSERT_INTG(push_last_dont_care_count_in_range_a,
                  push_valid && push_last |-> push_last_dont_care_count < SerializationRatio)
  `BR_ASSERT_INTG(push_last_dont_care_count_zero_a,
                  push_valid && !push_last |-> push_last_dont_care_count == 0)

  // Check push side validity and data stability
  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(PushWidth + 1 + SerFlitIdWidth + MetadataWidth),
      // Push ready/valid stability is required for the serializer to work correctly.
      // That's because it serially scans over the valid push data until the entire
      // packet has been transmitted. If the push data is unstable during
      // transmission, then the data integrity is compromised.
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({push_data, push_last, push_last_dont_care_count, push_metadata})
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Base case: pass-through.
  if (SerializationRatio == 1) begin : gen_sr_eq_1
    assign pop_valid = push_valid;
    assign pop_data = push_data;
    assign pop_last = push_last;
    assign pop_metadata = push_metadata;
    assign push_ready = pop_ready;
    `BR_UNUSED(push_last_dont_care_count)

    // General case: serialize.
  end else begin : gen_sr_gt_1

    //------
    // FSM is just an incrementing counter that keeps track of the pop flit ID.
    // When push_last is 0, then this simply counts up to SerializationRatio - 1
    // and then we complete the push flit. When push_last is 1, then we can complete
    // the push flit early when push_last_dont_care_count is not 0.
    //
    // Reinitialize the counter to 0 when we send the last pop flit.
    // If we finish serializing a push flit without the last bit, then we let the counter
    // naturally overflow to 0 on the next cycle (don't need to explicitly reinit).
    //------
    localparam int SrMinus1 = SerializationRatio - 1;
    logic                      pop_flit_id_reinit;
    logic                      pop_flit_id_incr_valid;
    logic [SerFlitIdWidth-1:0] pop_flit_id;

    br_counter_incr #(
        .ValueWidth(SerFlitIdWidth),
        .IncrementWidth(1),
        .MaxValue(SrMinus1),
        .MaxIncrement(1),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_counter_incr_pop_flit_id (
        .clk,
        .rst,
        .reinit(pop_flit_id_reinit),
        .initial_value(SerFlitIdWidth'(0)),
        .incr_valid(pop_flit_id_incr_valid),
        .incr(1'b1),
        .value(pop_flit_id),
        .value_next()  // unused
    );

    assign pop_flit_id_reinit = pop_ready && pop_valid && pop_last;
    // Need to qualify the increment on !pop_last because the counter supports reinit-and-increment in one cycle.
    assign pop_flit_id_incr_valid = pop_ready && pop_valid && !pop_last;

    //------
    // Calculate which slice of the push flit is muxed to the pop interface.
    // It depends on both the serialization order and the state of the counter.
    //------
    logic [SerFlitIdWidth-1:0] sr_minus_1;
    logic [SerFlitIdWidth-1:0] slice_id;

    assign sr_minus_1 = SrMinus1;
    assign slice_id   = SerializeMostSignificantFirst ? (sr_minus_1 - pop_flit_id) : pop_flit_id;

    //------
    // Do the muxing.
    //------
    br_mux_bin #(
        .NumSymbolsIn(SerializationRatio),
        .SymbolWidth (PopWidth)
    ) br_mux_bin (
        .select(slice_id),
        .in(push_data),
        .out(pop_data),
        .out_valid()
    );

    //------
    // Drive the rest of the pop interface outputs.
    // Terminate the pop stream early when it's the last push flit and
    // there are "don't care" slices at the tail of it.
    //
    // The metadata is replicated from the push side for each pop flit.
    //------
    logic [SerFlitIdWidth-1:0] pop_flit_id_plus_dont_care_count;

    assign pop_valid = push_valid;
    assign pop_flit_id_plus_dont_care_count = pop_flit_id + push_last_dont_care_count;
    assign pop_last = push_last && (pop_flit_id_plus_dont_care_count == sr_minus_1);
    assign pop_metadata = push_metadata;

    //------
    // Complete the push flit when we're finished serializing it (the last pop flit for
    // this push flit is accepted).
    //------

    // Note that this might be X when push_valid is 0, because pop_flit_id_plus_dont_care_count
    // has a fanin from push_data. That's ok, since 0 && X == 0. Keeping the valid off of the
    // fanin for push_ready improves timing and helps avoid combinational loops.
    assign push_ready = pop_ready && (pop_flit_id_plus_dont_care_count == sr_minus_1);

  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // TODO: standard ready-valid check modules
  `BR_ASSERT_IMPL(cut_through_latency_0_a, push_valid |-> pop_valid)
  `BR_ASSERT_IMPL(pop_last_a, pop_valid && pop_last |-> push_last)
  `BR_COVER_IMPL(dont_cares_c, push_valid && push_last && push_last_dont_care_count != 0)

endmodule : br_flow_serializer
