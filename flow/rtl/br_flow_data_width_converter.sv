// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Data Width Converter
//
// This module converts fixed-size packet payloads between different push-side and pop-side
// flit widths. Data flows from push-side to pop-side using ready-valid handshakes on both sides.
//
// Packet boundaries are implicit. Each pushed packet contains exactly PushFlitsPerPacket push flits
// and PacketDataWidth payload bits. Each popped packet contains exactly PopFlitsPerPacket pop flits
// and the same PacketDataWidth payload bits.
//
// When PacketDataWidth is not evenly divisible by a flit width, then only the least-significant
// tail bits of the last flit on that interface are valid packet payload bits. The remaining
// most-significant bits of that last flit are don't cares.
//
// The push_sideband is sampled only on the first push flit of each packet. It is queued separately
// from the payload data and replicated on every pop flit of the matching packet.
//
// The steady-state throughput is 1 push flit per cycle and 1 pop flit per cycle. Equivalently,
// assuming both interfaces remain ready and valid whenever possible, the sustainable packet
// initiation interval is max(PushFlitsPerPacket, PopFlitsPerPacket) cycles per packet.
//
// The latency from the first accepted push flit of a packet to the first pop flit becoming valid
// depends on how many push flits are needed to accumulate the first pop flit worth of payload bits.
// The minimum cut-through latency is 1 cycle, and the maximum is PushFlitsPerPacket cycles when
// the module must accumulate a full packet before it can emit the first pop flit.
//
// The implementation stores up to one packet plus one additional push flit of payload bits in a
// circular reservoir so that push and pop widths can differ without breaking packet boundaries.

`include "br_asserts_internal.svh"
`include "br_assign.svh"
`include "br_registers.svh"

module br_flow_data_width_converter #(
    // Width of each push-side flit. Must be at least 1.
    parameter int unsigned PushFlitDataWidth = 2,
    // Width of each pop-side flit. Must be at least 2 and no larger than BufferDataWidth.
    parameter int unsigned PopFlitDataWidth = 4,
    // Number of valid payload bits in each packet. Must be at least 1.
    parameter int unsigned PacketDataWidth = 8,
    // Number of push-side flits in each packet. Must be at least 1 and large enough to cover
    // PacketDataWidth payload bits.
    parameter int unsigned PushFlitsPerPacket = 2,
    // Number of pop-side flits in each packet. Must be at least 1 and large enough to cover
    // PacketDataWidth payload bits.
    parameter int unsigned PopFlitsPerPacket = 2,
    // Width of the packet sideband. Must be at least 1.
    parameter int unsigned SidebandWidth = 1,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    output logic                         push_ready,
    input  logic                         push_valid,
    input  logic [PushFlitDataWidth-1:0] push_data,
    // Sampled only on the first push flit of each packet.
    input  logic [    SidebandWidth-1:0] push_sideband,

    // Pop-side interface.
    input  logic                        pop_ready,
    output logic                        pop_valid,
    // On the last pop flit of a packet, only the least-significant PopTailDataWidth bits are valid
    // when PacketDataWidth is not evenly divisible by PopFlitDataWidth.
    output logic [PopFlitDataWidth-1:0] pop_data,
    // Replicated on every pop flit of the packet.
    output logic [   SidebandWidth-1:0] pop_sideband
);

  import br_math::*;

  localparam int unsigned BufferDataWidth = PacketDataWidth + PushFlitDataWidth;
  localparam int unsigned BufferCountWidth = $clog2(BufferDataWidth + 1);
  localparam int unsigned BufferPtrWidth = $clog2(BufferDataWidth);
  localparam int unsigned PushBitsWidth = $clog2(PushFlitDataWidth + 1);
  localparam int unsigned PopBitsWidth = $clog2(PopFlitDataWidth + 1);
  localparam int unsigned PushFlitIdWidth = clamped_clog2(PushFlitsPerPacket);
  localparam int unsigned PopFlitIdWidth = clamped_clog2(PopFlitsPerPacket);
  localparam int unsigned PushTailDataWidth =
      PacketDataWidth - ((PushFlitsPerPacket - 1) * PushFlitDataWidth);
  localparam int unsigned PopTailDataWidth =
      PacketDataWidth - ((PopFlitsPerPacket - 1) * PopFlitDataWidth);

  logic [                 BufferDataWidth-1:0] buffer_data;
  logic [                 BufferDataWidth-1:0] buffer_data_next;
  logic [BufferDataWidth+PopFlitDataWidth-2:0] buffer_data_ext;
  logic [                  BufferPtrWidth-1:0] wr_ptr;
  logic [                  BufferPtrWidth-1:0] rd_ptr;
  logic [                BufferCountWidth-1:0] total_bits_buffered;
  logic [                 PushFlitIdWidth-1:0] push_flit_id;
  logic [                  PopFlitIdWidth-1:0] pop_flit_id;
  logic [                   PushBitsWidth-1:0] push_payload_bits;
  logic [                    PopBitsWidth-1:0] pop_payload_bits;
  logic [                BufferCountWidth-1:0] push_payload_bits_ext;
  logic [                BufferCountWidth-1:0] pop_payload_bits_ext;
  logic [                BufferCountWidth-1:0] buffer_space_available;
  logic                                        push_first_flit;
  logic                                        push_last_flit;
  logic                                        pop_last_flit;
  logic                                        push;
  logic                                        pop;
  logic                                        sideband_push_ready;
  logic                                        sideband_push_valid;
  logic                                        sideband_pop_ready;
  logic                                        sideband_pop_valid;
  logic [                   SidebandWidth-1:0] sideband_pop_data;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(push_flit_data_width_gte_1_a, PushFlitDataWidth >= 1)
  `BR_ASSERT_STATIC(pop_flit_data_width_gte_2_a, PopFlitDataWidth >= 2)
  `BR_ASSERT_STATIC(packet_data_width_gte_1_a, PacketDataWidth >= 1)
  `BR_ASSERT_STATIC(sideband_width_gte_1_a, SidebandWidth >= 1)
  `BR_ASSERT_STATIC(push_flits_per_packet_gte_1_a, PushFlitsPerPacket >= 1)
  `BR_ASSERT_STATIC(pop_flits_per_packet_gte_1_a, PopFlitsPerPacket >= 1)
  `BR_ASSERT_STATIC(buffer_ptr_width_gte_1_a, BufferPtrWidth >= 1)
  `BR_ASSERT_STATIC(pop_flit_data_width_lte_buffer_data_width_a,
                    PopFlitDataWidth <= BufferDataWidth)
  `BR_ASSERT_STATIC(push_packet_covers_payload_a,
                    (PushFlitsPerPacket * PushFlitDataWidth) >= PacketDataWidth)
  `BR_ASSERT_STATIC(pop_packet_covers_payload_a,
                    (PopFlitsPerPacket * PopFlitDataWidth) >= PacketDataWidth)
  `BR_ASSERT_STATIC(push_tail_width_legal_a,
                    PushTailDataWidth >= 1 && PushTailDataWidth <= PushFlitDataWidth)
  `BR_ASSERT_STATIC(pop_tail_width_legal_a,
                    PopTailDataWidth >= 1 && PopTailDataWidth <= PopFlitDataWidth)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(PushFlitDataWidth + SidebandWidth),
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg_push (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({push_data, push_sideband})
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign push_first_flit = push_flit_id == '0;
  assign push_last_flit = push_flit_id == PushFlitIdWidth'(PushFlitsPerPacket - 1);
  assign pop_last_flit = pop_flit_id == PopFlitIdWidth'(PopFlitsPerPacket - 1);
  assign push_payload_bits = push_last_flit ? PushBitsWidth'(PushTailDataWidth)
                                            : PushBitsWidth'(PushFlitDataWidth);
  assign pop_payload_bits = pop_last_flit ? PopBitsWidth'(PopTailDataWidth)
                                          : PopBitsWidth'(PopFlitDataWidth);

  assign buffer_space_available = BufferDataWidth - total_bits_buffered;
  assign push_ready = (buffer_space_available >= push_payload_bits_ext) &&
                      (!push_first_flit || sideband_push_ready);
  assign push = push_valid && push_ready;
  assign pop_valid = sideband_pop_valid && (total_bits_buffered >= pop_payload_bits_ext);
  assign pop = pop_valid && pop_ready;
  assign sideband_push_valid = push && push_first_flit;
  assign sideband_pop_ready = pop && pop_last_flit;
  assign pop_sideband = sideband_pop_data;

  `BR_ASSIGN_MAYBE_ZERO_EXT(push_payload_bits_ext, push_payload_bits_ext, push_payload_bits)
  `BR_ASSIGN_MAYBE_ZERO_EXT(pop_payload_bits_ext, pop_payload_bits_ext, pop_payload_bits)

  assign buffer_data_ext = {buffer_data[PopFlitDataWidth-2:0], buffer_data};

  br_counter #(
      .MaxValue(BufferDataWidth),
      .MaxChange(BufferDataWidth),
      .MaxIncrement(PushFlitDataWidth),
      .MaxDecrement(PopFlitDataWidth),
      .EnableWrap(0),
      .EnableSaturate(0),
      .EnableReinitAndChange(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableCoverZeroChange(0),
      .EnableCoverReinit(0)
  ) br_counter_total_bits_buffered (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(push),
      .incr(push_payload_bits_ext),
      .decr_valid(pop),
      .decr(pop_payload_bits_ext),
      .value(total_bits_buffered),
      .value_next()  // unused
  );

  br_counter_incr #(
      .MaxValue(BufferDataWidth - 1),
      .MaxIncrement(PushFlitDataWidth),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableCoverZeroIncrement(0),
      .EnableCoverReinit(0)
  ) br_counter_incr_wr_ptr (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(push),
      .incr(push_payload_bits),
      .value(wr_ptr),
      .value_next()  // unused
  );

  br_counter_incr #(
      .MaxValue(BufferDataWidth - 1),
      .MaxIncrement(PopFlitDataWidth),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableCoverZeroIncrement(0),
      .EnableCoverReinit(0)
  ) br_counter_incr_rd_ptr (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(pop),
      .incr(pop_payload_bits),
      .value(rd_ptr),
      .value_next()  // unused
  );

  if (PushFlitsPerPacket == 1) begin : gen_push_flit_id_const
    assign push_flit_id = '0;
  end else begin : gen_push_flit_id_counter
    br_counter_incr #(
        .MaxValue(PushFlitsPerPacket - 1),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableCoverZeroIncrement(0),
        .EnableCoverReinit(0)
    ) br_counter_incr_push_flit_id (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value('0),
        .incr_valid(push),
        .incr(1'b1),
        .value(push_flit_id),
        .value_next()  // unused
    );
  end

  if (PopFlitsPerPacket == 1) begin : gen_pop_flit_id_const
    assign pop_flit_id = '0;
  end else begin : gen_pop_flit_id_counter
    br_counter_incr #(
        .MaxValue(PopFlitsPerPacket - 1),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableCoverZeroIncrement(0),
        .EnableCoverReinit(0)
    ) br_counter_incr_pop_flit_id (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value('0),
        .incr_valid(pop),
        .incr(1'b1),
        .value(pop_flit_id),
        .value_next()  // unused
    );
  end

  always_comb begin
    buffer_data_next = buffer_data;
    if (push) begin
      // ri lint_check_waive VAR_INDEX_WRITE
      buffer_data_next[wr_ptr+:PushFlitDataWidth] = push_data;
    end
  end

  assign pop_data = buffer_data_ext[rd_ptr+:PopFlitDataWidth];

  br_flow_reg_both #(
      .Width(SidebandWidth),
      .EnableCoverPushBackpressure(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_reg_both_sideband (
      .clk,
      .rst,
      .push_ready(sideband_push_ready),
      .push_valid(sideband_push_valid),
      .push_data (push_sideband),
      .pop_ready (sideband_pop_ready),
      .pop_valid (sideband_pop_valid),
      .pop_data  (sideband_pop_data)
  );

  `BR_REGN(buffer_data, buffer_data_next)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(PopFlitDataWidth + SidebandWidth),
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl_pop (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data ({pop_data, pop_sideband})
  );

  `BR_ASSERT_IMPL(push_flit_id_wrap_a, push && push_last_flit |=> push_flit_id == '0)
  `BR_ASSERT_IMPL(pop_flit_id_wrap_a, pop && pop_last_flit |=> pop_flit_id == '0)
  `BR_ASSERT_IMPL(push_implies_buffer_has_space_a,
                  push |-> buffer_space_available >= push_payload_bits_ext)
  `BR_ASSERT_IMPL(pop_implies_buffer_has_data_a,
                  pop |-> total_bits_buffered >= pop_payload_bits_ext)

endmodule : br_flow_data_width_converter
