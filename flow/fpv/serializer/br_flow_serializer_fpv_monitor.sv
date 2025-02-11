// Bedrock-RTL Flow Serializer
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
`include "br_registers.svh"

module br_flow_serializer_fpv_monitor #(
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
    input logic clk,
    input logic rst,

    // Push-side interface (wide flits).
    input logic                      push_ready,
    input logic                      push_valid,
    input logic [     PushWidth-1:0] push_data,
    input logic                      push_last,
    input logic [SerFlitIdWidth-1:0] push_last_dont_care_count,
    input logic [ MetadataWidth-1:0] push_metadata,

    // Pop-side interface (narrow, serialized flits).
    input logic                     pop_ready,
    input logic                     pop_valid,
    input logic [     PopWidth-1:0] pop_data,
    input logic                     pop_last,
    input logic [MetadataWidth-1:0] pop_metadata
);

  // cnt value is from 0 to SerializationRatio - 1
  localparam int MAX = SerializationRatio - 1;
  logic [SerFlitIdWidth-1:0] fv_care_max;
  logic [SerFlitIdWidth-1:0] fv_flit_cnt;

  // ----------FV assumptions----------
  // push payload must be held stable until push_ready is 1.
  `BR_ASSUME(push_payload_stable_a, push_valid && !push_ready |=> $stable
                                    ({push_valid, push_data, push_last, push_last_dont_care_count,
                                      push_metadata}))
  // Number of dont_care flits should not exceed SerializationRatio
  `BR_ASSUME(legal_dont_care_count_a,
             push_valid & push_last |-> push_last_dont_care_count < SerializationRatio)
  `BR_ASSUME(dont_care_count_quiet_a, push_valid & !push_last |-> push_last_dont_care_count == 'd0)

  // ----------FV assertions----------
  // if PushWidth=32, PopWidth=8, SerializationRatio=4.
  // push_data = 32'h89ABCDEF
  // SerializeMostSignificantFirst = 1, then pop_data will be 89,AB,CD,EF
  // SerializeMostSignificantFirst = 0, then pop_data will be EF,CD,AB,89
  // For these 4 cycles: fv_flit_cnt = 0,1,2,3

  // push_last_dont_care_count indicates don't care flits.
  // if push_last_dont_care_count = 1, the last flip is don't care.
  // SerializeMostSignificantFirst = 1 as an example:
  //    For first 3-cyc, pop_data will be 89,AB,CD.
  //    Then last cyc, pop_data is a dont care.
  assign fv_care_max = MAX - push_last_dont_care_count;

  // fv_flit_cnt will cap at fv_care_max
  `BR_REGL(fv_flit_cnt, fv_flit_cnt != fv_care_max ? fv_flit_cnt + 'd1 : 'd0, pop_valid & pop_ready)

  // lower index and higher index of push_data.
  // SerializeMostSignificantFirst = 0 as an example:
  // For these 4 cycles: fv_flit_cnt = 0,1,2,3
  // corresponding push_data is: [7:0],[15:8],[23:16],[31:24]
  for (genvar i = 0; i < SerializationRatio; i++) begin : gen_ast
    if (SerializeMostSignificantFirst) begin : gen_msb
      `BR_ASSERT(data_integrity_a,
                 pop_valid && (fv_flit_cnt == i) |->
      pop_data == push_data[PopWidth*(MAX-i)+PopWidth-1:PopWidth*(MAX-i)])
    end else begin : gen_lsb
      `BR_ASSERT(data_integrity_a,
                 pop_valid && (fv_flit_cnt == i) |->
      pop_data == push_data[PopWidth*i+PopWidth-1:PopWidth*i])
    end
  end

  // push_ready should be asserted for last flit.
  `BR_ASSERT(push_ready_check_a, push_ready |-> (fv_flit_cnt == fv_care_max))
  `BR_ASSERT(pop_valid_check_a, push_valid == pop_valid)
  `BR_ASSERT(metadata_check_a, pop_valid |-> pop_metadata == push_metadata)
  `BR_ASSERT(no_pop_last_check_a,
             push_valid && (!push_last || (fv_flit_cnt < fv_care_max)) |-> !pop_last)
  `BR_ASSERT(pop_last_check_a, push_valid && push_last && (fv_flit_cnt == fv_care_max) |-> pop_last)
  `BR_ASSERT(pop_payload_stable_a, pop_valid && !pop_ready |=> $stable({pop_valid, pop_data,
                                                                        pop_last, pop_metadata}))

  // ----------Critical Covers----------
  `BR_COVER(dont_care_c, push_valid && push_last && (push_last_dont_care_count != 'd0))
  `BR_COVER(fake_dont_care_c, push_valid && push_last && (push_last_dont_care_count == 'd0))

endmodule : br_flow_serializer_fpv_monitor

bind br_flow_serializer br_flow_serializer_fpv_monitor #(
    .PushWidth(PushWidth),
    .PopWidth(PopWidth),
    .MetadataWidth(MetadataWidth),
    .SerializeMostSignificantFirst(SerializeMostSignificantFirst),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
