// SPDX-License-Identifier: Apache-2.0

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
