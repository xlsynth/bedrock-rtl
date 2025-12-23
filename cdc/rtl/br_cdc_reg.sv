// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL CDC Register
//
// A simple CDC crossing with a single multi-bit storage element.
// To be used for low-bandwidth multi-bit channels where a low-cost
// CDC crossing is needed. This is essentially the same as br_cdc_fifo_flops
// with Depth = 1 (a configuration not allowed by br_cdc_fifo_flops itself).
//
// The cut-through latency is (RegisterResetActive + 1) * PushT + (NumSyncStages + RegisterPopOutputs) * PopT and
// the backpressure latency is (RegisterResetActive + 1) * PopT + NumSyncStages * PushT
// where PushT and PopT are the push and pop clock periods, respectively.
// At steady-state, the throughput is 1 transaction every
// (RegisterResetActive + 1 + NumSyncStages) * (PushT + PopT).

module br_cdc_reg #(
    parameter int Width = 1,  // Must be at least 1
    // If 1, make sure pop_data is registered on the pop_clk at the cost of an
    // additional pop cycle of latency and `Width` extra bits of flops.
    // If 0, pop_data will be read asynchronously from a push_clk register.
    parameter bit RegisterPopOutputs = 0,
    // If 1 (the default), register push_rst on push_clk and pop_rst on pop_clk
    // before sending to the CDC synchronizers. This adds one cycle to the cut-through
    // latency and one cycle to the backpressure latency.
    // Do not set this to 0 unless push_rst and pop_rst are driven directly by
    // registers.
    parameter bit RegisterResetActive = 1,
    // Number of synchronization stages to use. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumSyncStages = 3
) (
    // Push-side interface
    input  logic             push_clk,
    input  logic             push_rst,
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Pop-side interface
    input  logic             pop_clk,
    input  logic             pop_rst,
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  // Integration Assertions
  // Relay on integration checks in internal modules.

  // Implementation
  logic push_reset_active_push;
  logic push_push_flag;
  logic push_reset_active_pop;
  logic pop_push_flag;
  logic [Width-1:0] push_reg_data;
  logic pop_reset_active_push;
  logic push_pop_flag;
  logic pop_reset_active_pop;
  logic pop_pop_flag;

  // Push side
  br_cdc_reg_push #(
      .Width(Width),
      .RegisterResetActive(RegisterResetActive)
  ) br_cdc_reg_push (
      .clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rst(push_rst),
      .push_ready,
      .push_valid,
      .push_data,
      .reset_active_push(push_reset_active_push),
      .push_flag(push_push_flag),
      .push_reg_data,
      .reset_active_pop(push_reset_active_pop),
      .pop_flag(push_pop_flag)
  );

  // Pop side
  br_cdc_reg_pop #(
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive)
  ) br_cdc_reg_pop (
      .clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rst(pop_rst),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .reset_active_push(pop_reset_active_push),
      .push_flag(pop_push_flag),
      .push_reg_data,
      .reset_active_pop(pop_reset_active_pop),
      .pop_flag(pop_pop_flag)
  );

  // Push-to-Pop synchronization
  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_push_to_pop_reset_active (
      .src_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(1'b0),
      .src_bit(push_reset_active_push),
      .dst_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(1'b0),
      .dst_bit(pop_reset_active_push)
  );

  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_push_to_pop_flag (
      .src_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(push_rst),
      .src_bit(push_push_flag),
      .dst_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(pop_rst),
      .dst_bit(pop_push_flag)
  );

  // Pop-to-Push synchronization
  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_pop_to_push_reset_active (
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(1'b0),
      .src_bit(pop_reset_active_pop),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(1'b0),
      .dst_bit(push_reset_active_pop)
  );

  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_pop_to_push_flag (
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(pop_rst),
      .src_bit(pop_pop_flag),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(push_rst),
      .dst_bit(push_pop_flag)
  );

endmodule : br_cdc_reg
