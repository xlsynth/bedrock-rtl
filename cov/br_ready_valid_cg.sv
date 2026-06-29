// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL ready/valid functional coverage monitor.

`include "br_asserts.svh"

module br_ready_valid_cg #(
    parameter int PayloadWidth = 1
) (
    input logic clk,
    input logic rst,

    input logic                    valid,
    input logic                    ready,
    input logic [PayloadWidth-1:0] payload
);

  logic prev_valid;
  logic prev_ready;
  logic [PayloadWidth-1:0] prev_payload;

  covergroup ready_valid_cg with function sample (
      logic valid_sample,
      logic ready_sample,
      logic [PayloadWidth-1:0] payload_sample,
      logic prev_valid_sample,
      logic prev_ready_sample,
      logic [PayloadWidth-1:0] prev_payload_sample
  );
    option.per_instance = 1;

    valid_ready_state: coverpoint {
      valid_sample, ready_sample
    } {
      bins valid_backpressured = {2'b10};
      bins ready_waiting_for_valid = {2'b01};
      bins valid_before_ready = (2'b10 => 2'b11);
      bins ready_before_valid = (2'b01 => 2'b11);
      bins same_cycle_handshake = (2'b00 => 2'b11);
      bins single_cycle_transfer = (2'b00 => 2'b11 => 2'b00);
      bins back_to_back_transfers = (2'b11 => 2'b11);
    }

    payload_stable_while_valid_backpressured: coverpoint (
        payload_sample === prev_payload_sample
    ) iff (prev_valid_sample && !prev_ready_sample && valid_sample && !ready_sample) {
      bins stable = {1'b1};
    }
  endgroup

  ready_valid_cg ready_valid_cov = new();

  `BR_COVER_CR(multi_cycle_stall_then_transfer_c,
               ({valid, ready} == 2'b10) [* 2: $] ##1
               ({valid, ready} == 2'b11), clk, rst)

  always_ff @(posedge clk) begin
    if (rst) begin
      prev_valid   <= 1'b0;
      prev_ready   <= 1'b0;
      prev_payload <= '0;
    end else begin
      ready_valid_cov.sample(valid, ready, payload, prev_valid, prev_ready, prev_payload);

      prev_valid   <= valid;
      prev_ready   <= ready;
      prev_payload <= payload;
    end
  end

endmodule
