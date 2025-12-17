// SPDX-License-Identifier: Apache-2.0

// Pop side of Bedrock-RTL CDC Register

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_cdc_reg_pop #(
    parameter int Width = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterResetActive = 1
) (
    input logic clk,
    input logic rst,

    input logic pop_ready,
    output logic pop_valid,
    output logic [Width-1:0] pop_data,

    input logic reset_active_push,
    input logic push_flag,
    input logic [Width-1:0] push_reg_data,

    output logic reset_active_pop,
    output logic pop_flag
);
  // Integration Checks
  // None so far

  // Implementation
  localparam int PopResetDelay = RegisterResetActive ? 1 : 0;
  localparam int PopFlagDelay = PopResetDelay + 1;

  logic push_flag_saved;
  logic push_flag_visible;

  logic pop_flag_int;
  logic pop_flag_int_next;
  logic internal_pop_ready;
  logic internal_pop_valid;

  assign push_flag_visible = reset_active_push ? push_flag_saved : push_flag;
  // If push and pop flag are different, the data is valid
  assign internal_pop_valid = push_flag_visible != pop_flag_int;
  assign pop_flag_int_next =
      (internal_pop_valid && internal_pop_ready) ? ~pop_flag_int : pop_flag_int;

  `BR_REG(pop_flag_int, pop_flag_int_next)
  `BR_REGL(push_flag_saved, push_flag, !reset_active_push)

  br_delay_nr #(
      .Width(1),
      .NumStages(PopResetDelay)
  ) br_delay_nr_reset_active_pop (
      .clk,
      .in(rst),
      .out(reset_active_pop),
      .out_stages()
  );

  br_delay_nr #(
      .Width(1),
      .NumStages(PopFlagDelay)
  ) br_delay_nr_pop_flag (
      .clk,
      // Use pop_flag_int_next as the input instead of pop_flag_int
      // This ensures that the delay while entering reset matches that of reset_active_pop
      // but does not affect the cut-through latency.
      .in(pop_flag_int_next),
      .out(pop_flag),
      .out_stages()
  );

  if (RegisterPopOutputs) begin : gen_reg_out
    br_flow_reg_fwd #(
        .Width(Width)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(internal_pop_ready),
        .push_valid(internal_pop_valid),
        .push_data (push_reg_data),
        .pop_ready (pop_ready),
        .pop_valid (pop_valid),
        .pop_data  (pop_data)
    );
  end else begin : gen_passthru_out
    assign pop_valid = internal_pop_valid;
    assign pop_data = push_reg_data;
    assign internal_pop_ready = pop_ready;
  end

  // Implementation Checks
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(Width)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data (pop_data)
  );

endmodule : br_cdc_reg_pop
