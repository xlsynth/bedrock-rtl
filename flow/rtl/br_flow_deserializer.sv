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

// Bedrock-RTL Flow Deserializer
//
// This module deserializes an input packet consisting of multiple narrower flits into a single wider flit.
// Data flows from pop-side to push-side using ready-valid handshakes on both sides.
//
// The push and pop bitwidths are parameterized; the PopWidth must be a positive integer
// that is greater than PushWidth and is also divisible by PushWidth.
// The number of deserialized flits per packet is a constant given by PopWidth / PushWidth.
//
// The deserialization order is configured by DeserializeMostSignificantFirst. If 1, then the first flit
// is placed in the most significant bits of the pop data; otherwise, the last flit is placed there.
// The order of bits within each push flit is always maintained on the pop side.
//
// Although the number of push flits per packet is constant, each push flit is accompanied by a
// push_id sideband signal. This is useful for any logic that needs to directly operate on data within the
// serialized flow. For convenience, a push_last signal is also provided in case the user only needs to know
// when a deserialized packet is complete (equivalent to push_id == (NumPushFlits-1)).
//
// The push_valid and push_data must be held stable until push_ready is 1.
//
// The throughput of this module is 1 push flit per cycle; equivalently, a packet output interval of
// 1 packet per (PushWidth / PopWidth) cycles.
//
// Examples(where the ready and valid signals are not shown:
//
//     PushWidth = 8, PopWidth = 64, DeserializeMostSignificantFirst = 1
//     Cycle | push_data | push_id | push_last | pop_data
//     ------|-----------|---------|-----------|--------------
//     0     | 8'hBA     | 2'd0    | 1'b0      | 64'hBAxxxxxx
//     1     | 8'hAD     | 2'd1    | 1'b0      | 64'hBAADxxxx
//     2     | 8'hF0     | 2'd2    | 1'b0      | 64'hBAADF0xx
//     3     | 8'h0D     | 2'd3    | 1'b1      | 64'hBAADF00D
//
//     PushWidth = 8, PopWidth = 64, DeserializeMostSignificantFirst = 0
//     Cycle | push_data | push_id | push_last | pop_data
//     ------|-----------|---------|-----------|--------------
//     0     | 8'h0D     | 2'd0    | 1'b0      | 64'hxxxxxx0D
//     1     | 8'hF0     | 2'd1    | 1'b0      | 64'hxxxxF00D
//     2     | 8'hAD     | 2'd2    | 1'b0      | 64'hxxADF00D
//     3     | 8'hBA     | 2'd3    | 1'b1      | 64'hBAADF00D

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_flow_deserializer #(
    // Width of the push side flit. Must be at least 1.
    parameter int PushWidth = 1,
    // Width of the pop side packet. Must be greater than PushWidth
    // and evenly divisible by PushWidth.
    parameter int PopWidth = 2,
    // If 1, the most significant bits of the packet are received first.
    // If 0, the least significant bits are received first.
    // The order of bits within each flit is always the same that they
    // appear on the push interface.
    parameter bit DeserializeMostSignificantFirst = 1,
    localparam int NumPushFlits = PopWidth / PushWidth,
    localparam int PushFlitIdWidth = $clog2(NumPushFlits)
) (
    // Posedge-triggered clock
    input logic clk,
    // Synchronous active-high reset
    input logic rst,

    // Push-side interface (narrow, serialized)
    output logic                       push_ready,
    input  logic                       push_valid,
    input  logic [      PushWidth-1:0] push_data,
    input  logic [PushFlitIdWidth-1:0] push_id,
    input  logic                       push_last,

    // Pop-side interface (wide)
    input  logic                pop_ready,
    output logic                pop_valid,
    output logic [PopWidth-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  localparam int NumPushFlitsMinus1 = NumPushFlits - 1;

  `BR_ASSERT_STATIC(push_width_gte_1_a, PushWidth >= 1)
  `BR_ASSERT_STATIC(pop_width_multiple_of_push_width_a, (PopWidth % PushWidth) == 0)
  `BR_ASSERT_STATIC(pop_width_greater_than_push_width_a, PopWidth > PushWidth)

  `BR_ASSERT_INTG(push_id_in_range_a, push_valid |-> push_id < NumPushFlits)
  // TODO(mgottscho): check that push_id always increments by 1 and wraps around as expected.
  `BR_ASSERT_INTG(push_last_a, push_valid && push_id == NumPushFlitsMinus1 |-> push_last)

  br_flow_checks_valid_data #(
      .NumFlows(1),
      .Width(PushWidth + PushFlitIdWidth + 1),
      // Push ready/valid stability is required for the deserializer to work correctly.
      // That's because it serially receives the valid push data until the entire packet
      // has been received. If the push data is unstable during reception, then the data
      // integrity is compromised.
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1)
  ) br_flow_checks_valid_data (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({push_data, push_id, push_last})
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumPushFlits-1:0] internal_ready;
  logic [NumPushFlits-1:0] internal_valid;
  logic [NumPushFlits-1:0][PushWidth-1:0] internal_data;

  logic [NumPushFlits-1:0] internal_pop_ready;
  logic [NumPushFlits-1:0] internal_pop_valid;
  logic [NumPushFlits-1:0][PushWidth-1:0] internal_pop_data;

  br_flow_demux_select_unstable #(
      .NumFlows(NumPushFlits),
      .Width(PushWidth),
      .EnableCoverPushBackpressure(1),
      .EnableAssertPushValidStability(1),
      .EnableAssertPushDataStability(1)
  ) br_flow_demux_select_unstable (
      .clk,
      .rst,
      .select(push_id),
      .push_ready(push_ready),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(internal_ready),
      .pop_valid(internal_valid),
      .pop_data(internal_data)
  );

  // TODO(mgottscho): Simplify. We know by construction that internal_ready when visiting push_id > 0.
  // So we can omit some register logic.
  for (genvar i = 0; i < NumPushFlitsMinus1; i++) begin : gen_reg
    br_flow_reg_fwd #(
        .Width(PushWidth)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(internal_ready[i]),
        .push_valid(internal_valid[i]),
        .push_data (internal_data[i]),
        .pop_ready (internal_pop_ready[i]),
        .pop_valid (internal_pop_valid[i]),
        .pop_data  (internal_pop_data[i])
    );
  end

  // Only need to register the first N-1 flits, since the last flit can directly handshake with the pop side.
  assign internal_ready[NumPushFlits-1] = internal_pop_ready[NumPushFlits-1];
  assign internal_pop_valid[NumPushFlits-1] = internal_valid[NumPushFlits-1];
  assign internal_pop_data[NumPushFlits-1] = internal_data[NumPushFlits-1];

  // Concat & merge the pop interface; all deserialized flits must be synchronously popped.
  assign pop_valid = &internal_pop_valid;
  assign internal_pop_ready = {NumPushFlits{pop_ready && pop_valid}};

  if (DeserializeMostSignificantFirst) begin : gen_concat_msb_first
    for (genvar i = 0; i < NumPushFlits; i++) begin : gen_loop
      localparam int Lsb = ((NumPushFlits - i) - 1) * PushWidth;
      localparam int Msb = Lsb + PushWidth - 1;
      assign pop_data[Msb:Lsb] = internal_pop_data[i];
    end
  end else begin : gen_concat_lsb_first
    assign pop_data = internal_pop_data;  // concat
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // TODO: standard ready-valid check modules

  `BR_ASSERT_IMPL(pop_valid_iff_last_a, pop_valid |-> push_valid && push_last)

endmodule : br_flow_deserializer
