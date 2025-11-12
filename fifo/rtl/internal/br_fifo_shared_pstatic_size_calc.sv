// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO Size Calculation
//
// This is a simple module that computes the size of each logical FIFO
// from its base and bound addresses.
// It also performs error checking on the base and bound addresses to ensure that
// there is no misconfiguration. An error signal is asserted if there is.

`include "br_asserts_internal.svh"

module br_fifo_shared_pstatic_size_calc #(
    parameter int NumFifos = 1,
    parameter int Depth = NumFifos,

    localparam int AddrWidth  = br_math::clamped_clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Used only for assertions

    input logic [NumFifos-1:0][AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][AddrWidth-1:0] config_bound,
    output logic [NumFifos-1:0][CountWidth-1:0] config_size,
    output logic config_error
);
  // Integration checks
  `BR_ASSERT_INTG(config_base_stable, ##1 $stable(config_base))
  `BR_ASSERT_INTG(config_bound_stable, ##1 $stable(config_bound))

  logic [NumFifos-1:0] config_error_per_fifo;
  logic config_addr_oob;
  logic [NumFifos-1:0] config_base_gt_bound;
  logic [NumFifos-1:0] config_base_lte_prev_bound;

  if (br_math::is_power_of_2(Depth)) begin : gen_no_oob_check
    assign config_addr_oob = 1'b0;
  end else begin : gen_oob_check
    // Just check that the final bound is less than the depth
    // The other addresses are already checked to be less than
    // or equal to the final bound.
    assign config_addr_oob = config_bound[NumFifos-1] >= Depth;
  end

  for (genvar i = 0; i < NumFifos; i++) begin : gen_config_base_gt_bound
    logic [CountWidth-1:0] config_bound_excl;

    assign config_bound_excl = CountWidth'(config_bound[i]) + 1'b1;
    assign config_size[i] = config_bound_excl - CountWidth'(config_base[i]);

    assign config_base_gt_bound[i] = (config_base[i] > config_bound[i]);
  end

  assign config_base_lte_prev_bound[0] = 1'b0;
  for (genvar i = 1; i < NumFifos; i++) begin : gen_config_base_lte_prev_bound
    assign config_base_lte_prev_bound[i] = (config_base[i] <= config_bound[i-1]);
  end

  assign config_error_per_fifo = config_base_gt_bound | config_base_lte_prev_bound;
  assign config_error = config_addr_oob || (|config_error_per_fifo);
endmodule
