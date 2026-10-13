
`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_fifo_staging_circ_buf_ctrl #(
    // The depth of the buffer. Must be >= 1.
    parameter int Depth = 2
) (
    input logic clk,
    input logic rst,

    input logic advance_wr_ptr,
    input logic advance_rd_ptr,

    output logic [Depth-1:0] wr_ptr_onehot,
    output logic [Depth-1:0] rd_ptr_onehot,

    output logic empty,
    output logic full
);
  `BR_ASSERT_STATIC(legal_depth_a, Depth >= 2)

  // Use onehot-encoded pointers to avoid decoding logic
  logic [Depth-1:0] ptr_onehot_init;
  logic rd_ptr_shift_bit;
  logic wr_ptr_shift_bit;
  logic maybe_full, maybe_full_next;
  logic ptr_match;

  assign ptr_match = rd_ptr_onehot == wr_ptr_onehot;
  assign full = ptr_match && maybe_full;
  assign empty = ptr_match && !maybe_full;

  // Maybe-full becomes high when there is a push without pop
  // and goes low when there is a pop without push
  assign maybe_full_next = (advance_wr_ptr == advance_rd_ptr) ? maybe_full : advance_wr_ptr;

  assign ptr_onehot_init = Depth'(1'b1);

  // Left-Rotate by 1 to advance pointer
  // shift_out becomes shift in
  br_delay_shift_reg #(
      .Width(1),
      .NumStages(Depth),
      .EnableCoverReinit(0)
  ) br_delay_shift_reg_rd_ptr (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value(ptr_onehot_init),
      .value(rd_ptr_onehot),
      .shift_en(advance_rd_ptr),
      .shift_in(rd_ptr_shift_bit),
      .shift_out(rd_ptr_shift_bit)
  );

  br_delay_shift_reg #(
      .Width(1),
      .NumStages(Depth),
      .EnableCoverReinit(0)
  ) br_delay_shift_reg_wr_ptr (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value(ptr_onehot_init),
      .value(wr_ptr_onehot),
      .shift_en(advance_wr_ptr),
      .shift_in(wr_ptr_shift_bit),
      .shift_out(wr_ptr_shift_bit)
  );

  `BR_REG(maybe_full, maybe_full_next)
endmodule
