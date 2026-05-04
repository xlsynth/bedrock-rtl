// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for partial final deserialized words failing to zero-fill the tail.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_flow_deserializer_partial_zero_fill_fpv_repro #(
    parameter bit DeserializeMostSignificantFirst = 1
) (
    input logic clk,
    input logic rst
);
  localparam int PushWidth = 4;
  localparam int PopWidth = 16;
  localparam int MetadataWidth = 3;
  localparam int Ratio = PopWidth / PushWidth;
  localparam int FlitIdWidth = $clog2(Ratio);

  logic [3:0] cycle;
  logic push_ready;
  logic push_valid;
  logic [PushWidth-1:0] push_data;
  logic push_last;
  logic [MetadataWidth-1:0] push_metadata;
  logic pop_ready;
  logic pop_valid;
  logic [PopWidth-1:0] pop_data;
  logic pop_last;
  logic [FlitIdWidth-1:0] pop_last_dont_care_count;
  logic [MetadataWidth-1:0] pop_metadata;

  br_flow_deserializer #(
      .PushWidth(PushWidth),
      .PopWidth(PopWidth),
      .MetadataWidth(MetadataWidth),
      .DeserializeMostSignificantFirst(DeserializeMostSignificantFirst)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .push_last,
      .push_metadata,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_last,
      .pop_last_dont_care_count,
      .pop_metadata
  );

  always_comb begin
    unique case (cycle)
      4'd0: push_data = 4'ha;
      4'd1: push_data = 4'hb;
      4'd2: push_data = 4'hc;
      4'd3: push_data = 4'hd;
      4'd4: push_data = 4'h1;
      4'd5: push_data = 4'h2;
      4'd6: push_data = 4'h3;
      default: push_data = '0;
    endcase
  end

  assign push_valid = !rst && cycle < 7;
  assign push_last = cycle == 6;
  assign push_metadata = 3'h6;
  assign pop_ready = 1'b1;

  `BR_REG(cycle, cycle + 4'd1)

  if (DeserializeMostSignificantFirst) begin : gen_msf
    `BR_ASSERT(partial_tail_zero_fill_a,
               pop_valid && pop_last && pop_last_dont_care_count == 1 |-> pop_data[3:0] == '0)
  end else begin : gen_lsf
    `BR_ASSERT(partial_tail_zero_fill_a,
               pop_valid && pop_last && pop_last_dont_care_count == 1 |->
                   pop_data[PopWidth-1:PopWidth-PushWidth] == '0)
  end

endmodule : br_flow_deserializer_partial_zero_fill_fpv_repro
