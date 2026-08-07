// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL ready/valid functional coverage monitor.

`include "br_asserts.svh"
`include "br_registers.svh"

// This is a passive coverage monitor, so it intentionally has no outputs.
// ri lint_check_waive NO_OUTPUT
module br_ready_valid_covgrp #(
    parameter int DataWidth = 1
) (
    input logic clk,
    input logic rst,

    input logic                 valid,
    input logic                 ready,
    input logic [DataWidth-1:0] data
);

`ifdef SYNTHESIS
  `BR_ASSERT_STATIC(do_not_synthesize_br_ready_valid_covgrp_a, 0)
`endif

  `BR_ASSERT_STATIC(data_width_gte_1_a, DataWidth >= 1)

  logic prev_valid;
  logic prev_ready;
  logic [DataWidth-1:0] prev_data;

  // Coverpoints and crosses have implicit option and type_option members. The
  // linter incorrectly treats those standard members as duplicate declarations.
  // ri lint_check_off UNIQUE_NAMES
  // The covergroup sample function grammar does not permit an automatic lifetime.
  // ri lint_check_waive AUTOMATIC
  covergroup ready_valid_covgrp with function sample (
      // Coverpoints read these arguments, but the linter does not account for
      // covergroup references when checking sample function inputs.
      logic valid_sample,  // ri lint_check_waive INPUT_NOT_READ
      logic ready_sample,  // ri lint_check_waive INPUT_NOT_READ
      logic [DataWidth-1:0] data_sample,  // ri lint_check_waive INPUT_NOT_READ
      logic prev_valid_sample,  // ri lint_check_waive INPUT_NOT_READ
      logic prev_ready_sample,  // ri lint_check_waive INPUT_NOT_READ
      logic [DataWidth-1:0] prev_data_sample  // ri lint_check_waive INPUT_NOT_READ
  );
    option.per_instance = 1;

    cp_valid: coverpoint valid_sample {bins low = {1'b0}; bins high = {1'b1};}

    cp_ready: coverpoint ready_sample {bins low = {1'b0}; bins high = {1'b1};}

    valid_ready_state: cross cp_valid, cp_ready{
      bins valid_backpressured = binsof (cp_valid) intersect {1'b1} && binsof (cp_ready) intersect {
        1'b0
      };
      bins ready_waiting_for_valid = binsof(cp_valid) intersect {1'b0} &&
                                     binsof(cp_ready) intersect {
        1'b1
      };
      ignore_bins idle = binsof (cp_valid) intersect {1'b0} && binsof (cp_ready) intersect {1'b0};
      ignore_bins transfer = binsof (cp_valid) intersect {1'b1} && binsof (cp_ready) intersect {
        1'b1
      };
    }

    // Transition bins are only supported on coverpoints, not crosses.
    valid_ready_transition: coverpoint {
      valid_sample, ready_sample
    } {
      bins valid_before_ready = (2'b10 => 2'b11);
      bins ready_before_valid = (2'b01 => 2'b11);
      bins same_cycle_handshake = (2'b00 => 2'b11);
      bins single_cycle_transfer = (2'b00 => 2'b11 => 2'b00);
      bins back_to_back_transfers = (2'b11 => 2'b11);
    }

    data_stable_while_valid_backpressured: coverpoint (
        data_sample === prev_data_sample
    ) iff (
        prev_valid_sample && !prev_ready_sample && valid_sample && !ready_sample &&
        !$isunknown(
        {data_sample, prev_data_sample}
    )) {
      bins stable = {1'b1};
    }
  endgroup
  // ri lint_check_on UNIQUE_NAMES

  // Covergroups are verification-only constructs and require construction.
  ready_valid_covgrp ready_valid_cov = new();  // ri lint_check_waive INIT_ASSIGN

  `BR_COVER_CR(multi_cycle_stall_then_transfer_c,
               ({valid, ready} == 2'b10) [* 2: $] ##1
               ({valid, ready} == 2'b11), clk, rst)

  always_ff @(posedge clk) begin
    if (rst) begin
      ready_valid_cov.sample(1'b0, 1'b0, '0, 1'b0, 1'b0, '0);
    end else begin
      ready_valid_cov.sample(valid, ready, data, prev_valid, prev_ready, prev_data);
    end
  end

  `BR_REG(prev_valid, valid)
  `BR_REG(prev_ready, ready)
  `BR_REG(prev_data, data)

endmodule
