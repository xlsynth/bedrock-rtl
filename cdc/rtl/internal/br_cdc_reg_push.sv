// SPDX-License-Identifier: Apache-2.0

// Push side of Bedrock-RTL CDC Register

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_cdc_reg_push #(
    parameter int Width = 1,
    parameter bit RegisterResetActive = 1
) (
    input logic clk,
    input logic rst,
    output logic push_ready,
    input logic push_valid,
    input logic [Width-1:0] push_data,

    output logic reset_active_push,
    output logic push_flag,
    output logic [Width-1:0] push_reg_data,

    input logic reset_active_pop,
    input logic pop_flag
);
  // Integration Checks
  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(Width)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  // Implementation
  localparam int PushResetDelay = RegisterResetActive ? 1 : 0;
  localparam int PushFlagDelay = PushResetDelay + 1;

  logic push_flag_int_next;
  logic push_flag_int;
  logic pop_flag_saved;
  logic pop_flag_visible;

  assign pop_flag_visible = reset_active_pop ? pop_flag_saved : pop_flag;
  // If push and pop flag match, the register is empty
  assign push_ready = push_flag_int == pop_flag_visible;
  assign push_flag_int_next = (push_valid && push_ready) ? ~push_flag_int : push_flag_int;

  `BR_REG(push_flag_int, push_flag_int_next)
  `BR_REGL(push_reg_data, push_data, push_valid && push_ready)
  `BR_REGL(pop_flag_saved, pop_flag, !reset_active_pop)

  br_delay_nr #(
      .Width(1),
      .NumStages(PushResetDelay)
  ) br_delay_nr_reset_active_push (
      .clk,
      .in(rst),
      .out(reset_active_push),
      .out_stages()
  );

  br_delay_nr #(
      .Width(1),
      .NumStages(PushFlagDelay)
  ) br_delay_nr_push_flag (
      .clk,
      // Use push_flag_int_next as the input instead of push_flag_int
      // This ensures that the delay while entering reset matches that of reset_active_push
      // but does not affect the cut-through latency.
      .in(push_flag_int_next),
      .out(push_flag),
      .out_stages()
  );

  // Implementation Checks
  // None so far

endmodule : br_cdc_reg_push
