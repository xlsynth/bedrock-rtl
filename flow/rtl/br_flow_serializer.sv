// Copyright 2024 The Bedrock-RTL Authors
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
// This module serializes an input packet consisting of exactly one flit into multiple narrower flits.
// Data flows from push-side to pop-side using ready-valid handshakes on both sides.
//
// The push and pop bitwidths are parameterized; the PushWidth must be a positive integer
// that is greater than PopWidth and is also divisible by PopWidth.
// The number of serialized flits per packet is a constant given by PopWidth / PushWidth.
//
// The serialization order is configured by SerializeMostSignificantFirst. If 1, then the most-significant
// bits of the packet are sent first; otherwise, the least-significant are sent first.
// The order of bits within the flit is always the same that they appear on the push interface.
//
// Although the number of pop flits per packet is constant, each pop flit is accompanied by a
// pop_id sideband signal. This is useful for any logic that needs to directly operate on data within the
// serialized flow. For convenience, a pop_last signal is also provided in case the user only needs to know
// when a serialized packet is complete (equivalent to pop_id == (NumPopFlits-1)).
//
// The push_valid and push_data must be held stable until push_ready is 1.
//
// The throughput of this module is 1 pop flit per cycle; equivalently, a packet initiation interval of
// 1 packet per (PopWidth / PushWidth) cycles.
//
// The cut-through latency of the push packet to the first pop flit is 0 cycles.
//
// Examples(where the ready and valid signals are not shown:
//
//     PushWidth = 64, PopWidth = 8, SerializeMostSignificantFirst = 1
//     Cycle | push_data    | pop_data | pop_id | pop_last
//     ------|--------------|----------|--------|---------
//     0     | 64'hBAADF00D | 8'hBA    | 2'd0   | 1'b0
//     1     | stable       | 8'hAD    | 2'd1   | 1'b0
//     2     | stable       | 8'hF0    | 2'd2   | 1'b0
//     3     | stable       | 8'h0D    | 2'd3   | 1'b1
//
//     PushWidth = 64, PopWidth = 8, SerializeMostSignificantFirst = 0
//     Cycle | push_data    | pop_data | pop_id | pop_last
//     ------|--------------|----------|--------|---------
//     0     | 64'hBAADF00D | 8'h0D    | 2'd0   | 1'b0
//     1     | stable       | 8'hF0    | 2'd1   | 1'b0
//     2     | stable       | 8'hAD    | 2'd2   | 1'b0
//     3     | stable       | 8'hBA    | 2'd3   | 1'b1

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_flow_serializer #(
    // Width of the push side packet. Must be greater than PopWidth
    // and evenly divisible by PopWidth.
    parameter int PushWidth = 2,
    // Width of the pop side flit. Must be at least 1.
    parameter int PopWidth = 1,
    // If 1, the most significant bits of the packet are sent first.
    // If 0, the least significant bits are sent first.
    // The order of bits within each flit is always the same that they
    // appear on the push interface.
    parameter bit SerializeMostSignificantFirst = 1,
    localparam int NumPopFlits = PushWidth / PopWidth,
    localparam int PopFlitIdWidth = $clog2(NumPopFlits)
) (
    // Posedge-triggered clock
    input logic clk,
    // Synchronous active-high reset
    input logic rst,

    // Push-side interface (wide).
    output logic                 push_ready,
    input  logic                 push_valid,
    input  logic [PushWidth-1:0] push_data,

    // Pop-side interface (narrow, serialized)
    input  logic                      pop_ready,
    output logic                      pop_valid,
    output logic [      PopWidth-1:0] pop_data,
    output logic [PopFlitIdWidth-1:0] pop_id,
    output logic                      pop_last
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(pop_width_gte_1_a, PopWidth >= 1)
  `BR_ASSERT_STATIC(push_width_multiple_of_pop_width_a, (PushWidth % PopWidth) == 0)
  `BR_ASSERT_STATIC(push_width_greater_than_pop_width_a, PushWidth > PopWidth)

  // Check push side validity and data stability
  br_flow_checks_valid_data #(
      .NumFlows(1),
      .Width(PushWidth),
      // Push ready/valid stability is required for the serializer to work correctly.
      // That's because it serially scans over the valid push data until the entire
      // packet has been transmitted. If the push data is unstable during
      // transmission, then the data integrity is compromised.
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1)
  ) br_flow_checks_valid_data (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int NumPopFlitsMinus1 = NumPopFlits - 1;
  logic [PopFlitIdWidth-1:0] num_pop_flits_minus_1;
  logic [PopFlitIdWidth-1:0] slice_id;
  logic                      pop_id_incr;

  br_counter_incr #(
      .MaxValue(NumPopFlitsMinus1),
      .MaxIncrement(1)
  ) br_counter_incr_pop_id (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(PopFlitIdWidth'(0)),
      .incr_valid(pop_id_incr),
      .incr(1'b1),
      .value(pop_id),
      .value_next()  // unused
  );

  assign pop_id_incr = pop_ready && pop_valid;

  assign num_pop_flits_minus_1 = NumPopFlitsMinus1;
  assign pop_last = (pop_id == num_pop_flits_minus_1);
  assign pop_valid = push_valid;
  assign push_ready = pop_ready && pop_last;
  assign slice_id = SerializeMostSignificantFirst ? (num_pop_flits_minus_1 - pop_id) : pop_id;

  br_mux_bin #(
      .NumSymbolsIn(NumPopFlits),
      .SymbolWidth (PopWidth)
  ) br_mux_bin (
      .select(slice_id),
      .in(push_data),
      .out(pop_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // TODO: standard ready-valid check modules
  `BR_ASSERT_IMPL(cut_through_latency_0_a, push_valid |-> pop_valid)
  `BR_ASSERT_IMPL(pop_id_in_range_a, pop_valid |-> pop_id < NumPopFlits)
  `BR_ASSERT_IMPL(pop_last_a, pop_valid && pop_id == NumPopFlitsMinus1 |-> pop_last)
  `BR_ASSERT_IMPL(push_ready_iff_pop_last_a, push_ready |-> pop_ready && pop_valid && pop_last)

endmodule : br_flow_serializer
