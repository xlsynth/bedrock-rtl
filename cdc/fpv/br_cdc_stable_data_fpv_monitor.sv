`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_stable_data_fpv_monitor #(
    parameter int Width = 1,
    parameter logic [Width-1:0] InitValue = '0,
    parameter bit EnableRegisterResetActive = 1,
    parameter int NumSyncStages = 3
) (
    // FV system clk and rst
    input logic clk,
    input logic rst,

    input logic src_clk,
    input logic src_rst,
    input logic src_valid,
    input logic [Width-1:0] src_data,

    input logic dst_clk,
    input logic dst_rst
);

  // ----------Instantiate DUT----------
  logic dst_updated;
  logic [Width-1:0] dst_data;

  br_cdc_stable_data #(
      .Width(Width),
      .InitValue(InitValue),
      .RegisterResetActive(EnableRegisterResetActive),
      .NumSyncStages(NumSyncStages)
  ) dut (
      .src_clk,
      .src_rst,
      .src_valid,
      .src_data,
      .dst_clk,
      .dst_rst,
      .dst_updated,
      .dst_data
  );

  // ----------FV Assumptions----------
  // Data gets lost if we assert src_valid too frequently.
  // Pick a relatively large number of cycles to hold between assertions.
  // TODO(masai): Figure out a better way to determine this value.
  localparam int MinStableCycles = 100;

  `BR_ASSUME_CR(src_valid_infrequent_a, src_valid |=> !src_valid [* MinStableCycles], src_clk,
                src_rst)
  `BR_ASSUME_CR(no_src_valid_during_any_reset_a, (src_rst | dst_rst) |-> !src_valid, src_clk,
                src_rst)

  // ----------Basic Checks----------
  `BR_ASSERT_CR(init_value_correct_a, $fell(dst_rst) |-> dst_data == InitValue, dst_clk, dst_rst)

  // ----------Data integrity Check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0),
      .MAX_PENDING(1)
  ) scoreboard (
      .incoming_clk(src_clk),
      .outgoing_clk(dst_clk),
      .rstN(!rst),
      .incoming_vld(src_valid),
      .incoming_data(src_data),
      .outgoing_vld(dst_updated),
      .outgoing_data(dst_data)
  );

endmodule : br_cdc_stable_data_fpv_monitor
