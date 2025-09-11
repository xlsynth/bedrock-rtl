// SPDX-License-Identifier: Apache-2.0

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
    parameter bit SerializeMostSignificantFirst = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, cover scenarios where push_last is asserted, if 0, assert that push_last
    // is never asserted.
    parameter bit EnableCoverPushLast = 1,
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

  if (EnableCoverPushLast) begin : gen_push_last_covered
    `BR_ASSERT_INTG(push_last_dont_care_count_in_range_a,
                    push_valid && push_last |-> push_last_dont_care_count < SerializationRatio)
  end else begin : gen_push_last_not_covered
    `BR_ASSERT_INTG(push_last_always_zero_a, push_valid |-> !push_last)
  end
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
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
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
        .MaxValue(SrMinus1),
        .MaxIncrement(1),
        .EnableCoverZeroIncrement(0),
        .EnableCoverReinitAndIncr(0),
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
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(PopWidth + 1 + MetadataWidth),
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data ({pop_data, pop_last, pop_metadata})
  );

  `BR_ASSERT_IMPL(cut_through_latency_0_a, push_valid |-> pop_valid)
  `BR_ASSERT_IMPL(pop_last_a, pop_valid && pop_last |-> push_last)
  if (SerializationRatio > 1 && EnableCoverPushLast) begin : gen_nonzero_dont_care_cover
    `BR_COVER_IMPL(dont_cares_c, push_valid && push_last && push_last_dont_care_count != 0)
  end

endmodule : br_flow_serializer
