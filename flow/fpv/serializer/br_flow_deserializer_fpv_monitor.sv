// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_flow_deserializer_fpv_monitor #(
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
    parameter bit DeserializeMostSignificantFirst = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int DeserializationRatio = PopWidth / PushWidth,
    // Vector widths cannot be 0, so we need to special-case when DeserializationRatio == 1
    // even though the pop_last_dont_care_count port will be unused downstream in that case.
    localparam int SerFlitIdWidth = DeserializationRatio > 1 ? $clog2(DeserializationRatio) : 1
) (
    input logic clk,
    input logic rst,

    // Push-side interface (wide flits).
    input logic                     push_ready,
    input logic                     push_valid,
    input logic [    PushWidth-1:0] push_data,
    input logic                     push_last,
    input logic [MetadataWidth-1:0] push_metadata,

    // Pop-side interface (narrow, serialized flits).
    input logic                      pop_ready,
    input logic                      pop_valid,
    input logic [      PopWidth-1:0] pop_data,
    input logic                      pop_last,
    input logic [SerFlitIdWidth-1:0] pop_last_dont_care_count,
    input logic [ MetadataWidth-1:0] pop_metadata
);

  localparam int MAX = DeserializationRatio - 1;
  logic [SerFlitIdWidth-1:0] fv_care_max;
  logic [SerFlitIdWidth-1:0] fv_flit_cnt;

  // ----------FV assumptions----------
  // push payload must be held stable until push_ready is 1.
  `BR_ASSUME(push_payload_stable_a, push_valid && !push_ready |=> $stable
                                    ({push_valid, push_data, push_last, push_metadata}))

  // ----------FV assertions----------
  // if PopWidth=32, PushWidth=8, DeserializationRatio=4.
  // push_data = 89,AB,CD,EF, at 4th cycle:
  // DeserializeMostSignificantFirst = 1, then pop_data will be 32'h89ABCDEF
  // DeserializeMostSignificantFirst = 0, then pop_data will be 32'hEFCDAB89
  // For these 4 cycles: fv_flit_cnt = 0,1,2,3

  // pop_last_dont_care_count indicates don't care flits.
  // When push_last asserts, pop_last will assert.
  // DeserializeMostSignificantFirst = 1 as an example:
  //    if 3rd cycle, push_last = 1,
  //    pop_last_dont_care_count will be calculated as 1.
  //    pop_data will be 32'h89ABCDXX, ignoring last flit
  assign fv_care_max = MAX - pop_last_dont_care_count;

  // fv_flit_cnt will cap at fv_care_max
  `BR_REGL(fv_flit_cnt, fv_flit_cnt != fv_care_max ? fv_flit_cnt + 'd1 : 'd0,
           push_valid & push_ready)

  if (DeserializationRatio > 1) begin : gen_deserialized
    logic [PopWidth-1:0] fv_pop_data;
    // lower index and higher index of pop_data.
    // DeserializeMostSignificantFirst = 0 as an example:
    // For these 4 cycles: fv_flit_cnt = 0,1,2,3
    // push_data will be assigned to pop_data[7:0],[15:8],[23:16],[31:24]
    for (genvar i = 0; i < DeserializationRatio; i++) begin : gen_ast
      localparam int Msb = DeserializeMostSignificantFirst ? PushWidth*(MAX+1-i) : PushWidth*(i+1);
      localparam int Lsb = DeserializeMostSignificantFirst ? PushWidth * (MAX - i) : PushWidth * i;

      `BR_ASSUME(fv_pop_data_stable_a, fv_flit_cnt != i |-> $stable(fv_pop_data[Msb-1:Lsb]))
      `BR_ASSUME(fv_pop_data_a, fv_flit_cnt == i |-> fv_pop_data[Msb-1:Lsb] == push_data)

      if (DeserializeMostSignificantFirst) begin : gen_msb
        localparam int PopMsb = PopWidth;
        localparam int PopLsb = PushWidth * i;
        `BR_ASSERT(data_integrity_a,
                   pop_valid && (pop_last_dont_care_count == i) |->
                  pop_data[PopMsb-1:PopLsb] == fv_pop_data[PopMsb-1:PopLsb])
      end else begin : gen_lsb
        localparam int PopMsb = PushWidth * (MAX + 1 - i);
        `BR_ASSERT(data_integrity_a,
                   pop_valid && (pop_last_dont_care_count == i) |->
                  pop_data[PopMsb-1:0] == fv_pop_data[PopMsb-1:0])
      end
    end
  end else begin : gen_pass_through
    `BR_ASSERT(data_integrity_a, pop_valid |-> pop_data == push_data)
  end

  // Number of dont_care flits should not exceed DeserializationRatio
  `BR_ASSERT(legal_dont_care_count_a,
             pop_valid & pop_last |-> pop_last_dont_care_count < DeserializationRatio)
  `BR_ASSERT(dont_care_count_quiet_a, pop_valid && !pop_last |-> pop_last_dont_care_count == 'd0)
  // when pop_data is still building, push_ready should be high
  // or for last flit, if pop_ready is high, push_ready should be high to accept/release last push_data
  `BR_ASSERT(
      push_ready_check_a,
      (fv_flit_cnt < fv_care_max) || ((fv_flit_cnt == fv_care_max) & pop_ready) |-> push_ready)
  `BR_ASSERT(pop_valid_check_a, push_valid && (fv_flit_cnt == fv_care_max) |-> pop_valid)
  `BR_ASSERT(metadata_check_a, pop_valid |-> pop_metadata == push_metadata)
  `BR_ASSERT(pop_last_check_a, push_valid && push_last |-> pop_last)
  `BR_ASSERT(pop_payload_stable_a, pop_valid && !pop_ready |=> $stable({pop_valid, pop_data,
                                                                        pop_last, pop_metadata,
                                                                        pop_last_dont_care_count}))

  // ----------Critical Covers----------
  if (DeserializationRatio != 1) begin : gen_cov
    `BR_COVER(dont_care_c, pop_valid & pop_last && (pop_last_dont_care_count != 'd0))
  end
  `BR_COVER(fake_dont_care_c, pop_valid & pop_last && (pop_last_dont_care_count == 'd0))

endmodule : br_flow_deserializer_fpv_monitor

bind br_flow_deserializer br_flow_deserializer_fpv_monitor #(
    .PushWidth(PushWidth),
    .PopWidth(PopWidth),
    .MetadataWidth(MetadataWidth),
    .DeserializeMostSignificantFirst(DeserializeMostSignificantFirst),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
