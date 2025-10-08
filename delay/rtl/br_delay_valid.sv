// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Delay Line (With Valid)
//
// Delays a valid input signal by a fixed number of clock cycles.
// There are NumStages pipeline registers. If NumStages is 0,
// then the output is the input. The valid registers are reset to 0
// but the datapath registers are not. Each datapath register is clock
// gated using the valid signal.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_valid #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0,  // Must be at least 0
    // If 1, the first data stage is not gated by the valid signal.
    // This might be necessary for floorplan block inputs to avoid
    // an In2Reg path on the in_valid signal.
    parameter bit FirstStageUngated = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // Positive edge-triggered. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          clk,
    // Synchronous active-high. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          rst,
    input  logic                          in_valid,
    input  logic [  Width-1:0]            in,
    output logic                          out_valid,
    // Output of last delay stage (delayed by NumStages cycles).
    output logic [  Width-1:0]            out,
    // Indicates the valid status of each delay stage.
    output logic [NumStages:0]            out_valid_stages,
    // Output of each delay stage. Note that out_stages[0] == in, and
    // out_stages[NumStages] == out.
    output logic [NumStages:0][Width-1:0] out_stages
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_zero_a, NumStages >= 0)

  `BR_COVER_INTG(in_valid_c, in_valid)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_a, !in_valid)
    `BR_ASSERT_FINAL(final_not_out_valid_a, !out_valid)
    `BR_ASSERT_FINAL(final_not_out_valid_stages_a, out_valid_stages == '0)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages:0] stage_valid;
  logic [NumStages:0][Width-1:0] stage;

  // always_comb instead of assign here to keep iverilog happy
  always_comb begin
    stage_valid[0] = in_valid;
    stage[0] = in;
  end

  if (NumStages > 0 && FirstStageUngated) begin : gen_ungated_stage
    // ri lint_check_waive BA_NBA_REG
    `BR_REG(stage_valid[1], stage_valid[0])
    // ri lint_check_waive BA_NBA_REG
    `BR_REGN(stage[1], stage[0])
  end

  localparam int FirstGatedStage = FirstStageUngated ? 2 : 1;

  for (genvar i = FirstGatedStage; i <= NumStages; i++) begin : gen_stages
    // ri lint_check_waive BA_NBA_REG
    `BR_REG(stage_valid[i], stage_valid[i-1])
    // ri lint_check_waive BA_NBA_REG
    `BR_REGLN(stage[i], stage[i-1], stage_valid[i-1])
  end

  assign out_valid = stage_valid[NumStages];
  assign out = stage[NumStages];
  assign out_valid_stages = stage_valid;
  assign out_stages = stage;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (NumStages == 0) begin : gen_zero_delay
    `BR_ASSERT_IMPL(valid_passthru_a, out_valid === in_valid)
    `BR_ASSERT_IMPL(data_passthru_a, in_valid |-> (out === in))
  end else begin : gen_pos_delay
    `BR_ASSERT_IMPL(valid_delay_a, ##NumStages out_valid == $past(in_valid, NumStages))
    `BR_ASSERT_IMPL(data_delay_a, in_valid |-> ##NumStages out_valid && out == $past(in, NumStages))
  end

endmodule : br_delay_valid
