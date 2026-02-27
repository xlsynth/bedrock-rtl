// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Data Width Converter

`include "br_asserts.svh"
`include "br_registers.svh"

module br_flow_data_width_converter_fpv_monitor #(
    parameter int unsigned PushFlitDataWidth = 43,
    parameter int unsigned PopFlitDataWidth = 64,
    parameter int unsigned PacketDataWidth = 128,
    parameter int unsigned PushFlitsPerPacket = 3,
    parameter int unsigned PopFlitsPerPacket = 2,
    parameter int unsigned SidebandWidth = 1
) (
    input logic clk,
    input logic rst,

    input logic                         push_ready,
    input logic                         push_valid,
    input logic [PushFlitDataWidth-1:0] push_data,
    input logic [    SidebandWidth-1:0] push_sideband,

    input logic                        pop_ready,
    input logic                        pop_valid,
    input logic [PopFlitDataWidth-1:0] pop_data,
    input logic [   SidebandWidth-1:0] pop_sideband
);

  import br_math::*;

  localparam int unsigned BufferDataWidth = PacketDataWidth + PushFlitDataWidth;
  localparam int unsigned PushFlitIdWidth = clamped_clog2(PushFlitsPerPacket);
  localparam int unsigned PopFlitIdWidth = clamped_clog2(PopFlitsPerPacket);
  localparam int unsigned PushTailDataWidth =
      PacketDataWidth - ((PushFlitsPerPacket - 1) * PushFlitDataWidth);
  localparam int unsigned PopTailDataWidth =
      PacketDataWidth - ((PopFlitsPerPacket - 1) * PopFlitDataWidth);

  logic                         push;
  logic                         pop;
  logic [  PushFlitIdWidth-1:0] fv_push_flit_id;
  logic [   PopFlitIdWidth-1:0] fv_pop_flit_id;
  logic [PushFlitDataWidth-1:0] fv_push_data_valid;
  logic [ PopFlitDataWidth-1:0] fv_pop_data_valid;
  logic [PushFlitDataWidth-1:0] push_data_for_checks;
  logic [ PopFlitDataWidth-1:0] pop_data_for_checks;
  logic [    SidebandWidth-1:0] fv_pop_packet_sideband;
  logic                         push_first_flit;
  logic                         push_last_flit;
  logic                         pop_first_flit;

  assign push = push_valid && push_ready;
  assign pop = pop_valid && pop_ready;
  assign push_first_flit = fv_push_flit_id == '0;
  assign push_last_flit = fv_push_flit_id == PushFlitIdWidth'(PushFlitsPerPacket - 1);
  assign pop_first_flit = fv_pop_flit_id == '0;

  always_ff @(posedge clk) begin
    if (rst) begin
      fv_push_flit_id <= '0;
    end else if (push) begin
      fv_push_flit_id <= push_last_flit ? '0 : fv_push_flit_id + 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      fv_pop_flit_id <= '0;
    end else if (pop) begin
      fv_pop_flit_id <= (fv_pop_flit_id == PopFlitIdWidth'(PopFlitsPerPacket - 1)) ?
          '0 : fv_pop_flit_id + 1'b1;
    end
  end

  always_comb begin
    fv_push_data_valid = '1;
    if (push_last_flit && (PushTailDataWidth < PushFlitDataWidth)) begin
      fv_push_data_valid = '0;
      for (int i = 0; i < PushTailDataWidth; i++) begin
        fv_push_data_valid[i] = 1'b1;
      end
    end
  end

  always_comb begin
    fv_pop_data_valid = '1;
    if ((fv_pop_flit_id == PopFlitIdWidth'(PopFlitsPerPacket - 1)) &&
        (PopTailDataWidth < PopFlitDataWidth)) begin
      fv_pop_data_valid = '0;
      for (int i = 0; i < PopTailDataWidth; i++) begin
        fv_pop_data_valid[i] = 1'b1;
      end
    end
  end

  if (PushTailDataWidth < PushFlitDataWidth) begin : gen_push_data_for_checks_masked
    assign push_data_for_checks = push_last_flit ?
        {{(PushFlitDataWidth - PushTailDataWidth) {1'b0}}, push_data[PushTailDataWidth-1:0]} :
        push_data;
  end else begin : gen_push_data_for_checks_passthru
    assign push_data_for_checks = push_data;
  end

  if (PopTailDataWidth < PopFlitDataWidth) begin : gen_pop_data_for_checks_masked
    assign pop_data_for_checks = (fv_pop_flit_id == PopFlitIdWidth'(PopFlitsPerPacket - 1)) ?
        {{(PopFlitDataWidth - PopTailDataWidth) {1'b0}}, pop_data[PopTailDataWidth-1:0]} :
        pop_data;
  end else begin : gen_pop_data_for_checks_passthru
    assign pop_data_for_checks = pop_data;
  end

  `BR_REGL(fv_pop_packet_sideband, pop_sideband, pop_valid && pop_first_flit)

  // ----------FV assumptions----------
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))
  `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  `BR_ASSUME(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data_for_checks))
  `BR_ASSUME(push_sideband_stable_a, push_valid && push_first_flit && !push_ready |=> $stable
                                     (push_sideband))

  // ----------FV assertions----------
  `BR_ASSERT(pop_valid_stable_a, pop_valid && !pop_ready |=> pop_valid)
  `BR_ASSERT(pop_payload_stable_a, pop_valid && !pop_ready |=> $stable({pop_data_for_checks,
                                                                        pop_sideband}))
  `BR_ASSERT(pop_sideband_matches_packet_a,
             pop_valid && !pop_first_flit |-> pop_sideband == fv_pop_packet_sideband)

  // ----------Data integrity checks----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(1),
      .IN_CHUNKS(PushFlitDataWidth),
      .OUT_CHUNKS(PopFlitDataWidth),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(BufferDataWidth)
  ) payload_scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push ? fv_push_data_valid : '0),
      .incoming_data(push_data),
      .outgoing_vld(pop ? fv_pop_data_valid : '0),
      .outgoing_data(pop_data)
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(SidebandWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(2)
  ) sideband_scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push && push_first_flit),
      .incoming_data(push_sideband),
      .outgoing_vld(pop && pop_first_flit),
      .outgoing_data(pop_sideband)
  );

  // ----------Critical covers----------
  `BR_COVER(push_packet_c, push && push_last_flit)
  `BR_COVER(pop_packet_c, pop && (fv_pop_flit_id == PopFlitIdWidth'(PopFlitsPerPacket - 1)))

endmodule : br_flow_data_width_converter_fpv_monitor

bind br_flow_data_width_converter br_flow_data_width_converter_fpv_monitor #(
    .PushFlitDataWidth(PushFlitDataWidth),
    .PopFlitDataWidth(PopFlitDataWidth),
    .PacketDataWidth(PacketDataWidth),
    .PushFlitsPerPacket(PushFlitsPerPacket),
    .PopFlitsPerPacket(PopFlitsPerPacket),
    .SidebandWidth(SidebandWidth)
) monitor (.*);
