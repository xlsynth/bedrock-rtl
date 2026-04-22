// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Multicycle Path Marker
//
// Identifies a path as multicycle and adds assertions. The primary use of
// this is for constraint generation and design verification. This does not
// add any logic.
//
// To automatically instantiate this at the width of local logic,
// users can opt to use the convenience macros defined in macros/br_multicycle_path.svh.
//
// The path delay for setup is set by the CaptureCyclesShift parameter. This
// indicates the number of cycles between the launch and capture edges and
// would be 1 for a normal path.
//
// The minimum path delay is set by the CaptureCyclesWidth parameter. This
// determines which clock edge relative to the capture edge is used to check
// for hold time. Typically this would be set to (CaptureCyclesShift - 1).
// Other values are challenging for DFT.
//
// In simulation, this is modeled as a delay chain. To model hold behavior,
// x is injected onto any cycle where it is not legal to sample. This means
// that decreasing CaptureCyclesWidth reduces the amount of x injection.

`include "br_asserts_internal.svh"

module br_cdc_multicycle_path #(
    parameter int Width = 1,  // Must be at least 1
    parameter int CaptureCyclesShift = 1,  // Should be at least 1
    parameter bit AllowChangesOnlyInReset = 0,
    // Should be at least 0 and less than CaptureCyclesShift
    parameter int CaptureCyclesWidth = CaptureCyclesShift - 1
) (
    // Positive edge-triggered. Only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high. Only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    input  logic [Width-1:0] in,
    output logic [Width-1:0] out
);

  `BR_ASSERT_STATIC(capture_cycles_shift_gte_1_a, CaptureCyclesShift >= 1)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)
  `BR_ASSERT_STATIC(capture_cycles_width_gte_0_a, CaptureCyclesWidth >= 0)
  `BR_ASSERT_STATIC(capture_cycles_width_legal_a, CaptureCyclesWidth < CaptureCyclesShift)

  if (AllowChangesOnlyInReset) begin : gen_input_constraints
    `BR_ASSERT_INTG(in_stable_outside_reset_a, in == $past(in))
  end : gen_input_constraints

`ifdef SIMULATION
  // Model a delay of the input
  logic [CaptureCyclesShift-1:0][Width-1:0] in_delay;

  assign in_delay[0] = in;

  if (CaptureCyclesShift > 1) begin : gen_delay_chain
    always_ff @(posedge clk) begin
      in_delay <= {in_delay[CaptureCyclesShift-2:0], in};
    end
  end : gen_delay_chain

  // Check the most recent CaptureCyclesWidth entries and inject x if not the
  // same
  logic check_equivalence;

  always_comb begin
    check_equivalence = 1'b1;
    for (int i = 0; i < CaptureCyclesWidth; i++) begin
      check_equivalence &= in_delay[CaptureCyclesShift-1] == in_delay[CaptureCyclesShift-1-i];
    end
  end

  assign out = check_equivalence ? in_delay[CaptureCyclesShift-1] : 'x;

`else
  assign out = in;
`endif

endmodule : br_cdc_multicycle_path
