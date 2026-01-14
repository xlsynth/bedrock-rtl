// SPDX-License-Identifier: Apache-2.0


// Basic FPV checks for all CDC FIFO variations

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_fifo_basic_fpv_monitor #(
    parameter bit Jasper = 1,  // If 1 use Jasper scoreboard, else use Synopsys FML scoreboard
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int NumSyncStages = 3,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter int RamWriteLatency = 1,
    parameter int RamReadLatency = 1,
    parameter int PushExtraDelay = 0,
    parameter int PopExtraDelay = 0,
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // FV system clk and rst
    input logic clk,
    input logic rst,

    // Push-side interface.
    input logic             push_clk,
    input logic             push_rst,
    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface.
    input logic             pop_clk,
    input logic             pop_rst,
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,

    // Push-side status flags
    input logic push_full,
    input logic [CountWidth-1:0] push_slots,

    // Pop-side status flags
    input logic pop_empty,
    input logic [CountWidth-1:0] pop_items
);

  localparam int ResetActiveDelay = 1;
  // Adding ExtraDelay to account for any extra flops when instantiating br_cdc_fifo.
  // Need to make sure that on push reset, the updated push_count is not visible
  // to the pop side before reset_active is.
  localparam int PushCountDelay = PushExtraDelay +
                                  ((ResetActiveDelay + 1) >= RamWriteLatency ?
                                  (ResetActiveDelay + 1) : RamWriteLatency);
  // Need to make sure that on pop reset, the updated pop_count is not visible
  // to the push side before reset_active is.
  localparam int PopCountDelay = ResetActiveDelay + 1 + PopExtraDelay;

  // ----------FV assumptions----------
  `BR_ASSUME_CR(pop_ready_liveness_a, s_eventually (pop_ready), pop_clk, pop_rst)
  if (EnableCoverPushBackpressure) begin : gen_back_pressure
    if (EnableAssertPushValidStability) begin : gen_push_valid_stable
      `BR_ASSUME_CR(push_valid_stable_a, push_valid && !push_ready |=> push_valid, push_clk,
                    push_rst)
    end
    if (EnableAssertPushDataStability) begin : gen_push_data_stable
      `BR_ASSUME_CR(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data), push_clk,
                    push_rst)
    end
  end else begin : gen_no_back_pressure
    `BR_ASSUME_CR(no_back_pressure_a, push_valid |-> push_ready, push_clk, push_rst)
  end

  // ----------FV Modeling Code----------
  logic push_vr;
  logic pop_vr;
  logic fv_push_full;
  logic fv_pop_empty;
  logic [CountWidth-1:0] fv_push_items, fv_push_slots;
  logic [CountWidth-1:0] fv_pop_items;

  // pop side info
  localparam int CW = 32;  //FV CountWidth;
  logic [CW-1:0] fv_pop_cnt;
  logic [CW-1:0] fv_pop_sync;
  logic [CW-1:0] fv_pop_sync_cnt;
  // push side info
  logic [CW-1:0] fv_push_cnt;
  logic [CW-1:0] fv_push_sync;
  logic [CW-1:0] fv_push_sync_cnt;

  assign push_vr = push_valid & push_ready;
  assign pop_vr  = pop_valid & pop_ready;
  // count number of valid push at push side
  `BR_REGX(fv_push_cnt, fv_push_cnt + push_vr, push_clk, push_rst)
  // count number of valid pop at pop side
  `BR_REGX(fv_pop_cnt, fv_pop_cnt + pop_vr, pop_clk, pop_rst)

  // number of valid pop synced to push side
  fv_delay #(
      .Width(CW),
      .NumStages(PopCountDelay - 1)  // -1 since fv_pop_cnt is flopped
  ) delay_pop_vr (
      .clk(pop_clk),
      .rst(rst),
      .in (fv_pop_cnt),
      .out(fv_pop_sync)
  );

  fv_delay #(
      .Width(CW),
      .NumStages(NumSyncStages)
  ) delay_pop_sync (
      .clk(push_clk),
      .rst(rst),
      .in (fv_pop_sync),
      .out(fv_pop_sync_cnt)
  );

  // number of valid push synced to pop side
  fv_delay #(
      .Width(CW),
      .NumStages(PushCountDelay - 1)  // -1 since fv_push_cnt is flopped
  ) delay_push_vr (
      .clk(push_clk),
      .rst(rst),
      .in (fv_push_cnt),
      .out(fv_push_sync)
  );

  fv_delay #(
      .Width(CW),
      .NumStages(NumSyncStages)
  ) delay_push_sync (
      .clk(pop_clk),
      .rst(rst),
      .in (fv_push_sync),
      .out(fv_push_sync_cnt)
  );

  assign fv_push_items = fv_push_cnt - fv_pop_sync_cnt;
  assign fv_push_slots = Depth - fv_push_items;
  assign fv_pop_items  = fv_push_sync_cnt - fv_pop_cnt;

  assign fv_push_full  = fv_push_items == Depth;
  assign fv_pop_empty  = fv_pop_items == 'd0;

  // ----------Sanity Check----------
  `BR_ASSERT_CR(no_ready_when_full_a, push_full |-> !push_ready, push_clk, push_rst)
  `BR_ASSERT_CR(no_pop_when_empty_a, pop_empty |-> !pop_valid, pop_clk, pop_rst)
  `BR_ASSERT_CR(pop_valid_ready_a, pop_valid && !pop_ready |=> pop_valid && $stable(pop_data),
                pop_clk, pop_rst)

  // empty, full check
  `BR_ASSERT_CR(push_full_a, fv_push_full == push_full, push_clk, push_rst)
  `BR_ASSERT_CR(pop_empty_a, fv_pop_empty == pop_empty, pop_clk, pop_rst)

  // slots, items check
  `BR_ASSERT_CR(pop_items_a, fv_pop_items == pop_items, pop_clk, pop_rst)
  `BR_ASSERT_CR(push_slots_a, fv_push_slots == push_slots, push_clk, push_rst)

  // ----------Data integrity Check----------
  if (Jasper) begin : gen_jasper
    jasper_scoreboard_3 #(
        .CHUNK_WIDTH(Width),
        .IN_CHUNKS(1),
        .OUT_CHUNKS(1),
        .SINGLE_CLOCK(0),
        .MAX_PENDING(Depth)
    ) scoreboard (
        .incoming_clk(push_clk),
        .outgoing_clk(pop_clk),
        .rstN(!rst),
        .incoming_vld(push_vr),
        .incoming_data(push_data),
        .outgoing_vld(pop_vr),
        .outgoing_data(pop_data)
    );
  end else begin : gen_snps
    snps_fml_scoreboard #(
        .DATA_CHUNK_WIDTH   (Width),
        .NUM_OF_IN_CHUNKS   (1),
        .NUM_OF_OUT_CHUNKS   (1),
        .MAX_OUTSTANDING_CHUNKS  (Depth),
        .ENABLE_INORDER (1),
        //       .CHKLT   (0),
        //       .MAXLT   (0),
        //       .CHKFL   (0),
        .ENABLE_DUAL_CLOCKS (1),
        .SCBMODE (0)
    ) scoreboard (
        .Resetn  (!rst),
        .ClkIn   (push_clk),
        .ValidIn (push_vr),
        .DataIn  (push_data),
        .ClkOut  (pop_clk),
        .ValidOut(pop_vr),
        .DataOut (pop_data)
    );
  end

  // ----------Forward Progress Check----------
  if (EnableAssertPushValidStability) begin : gen_stable
    `BR_ASSERT(no_deadlock_pop_a, push_valid |-> s_eventually pop_valid)
  end else begin : gen_not_stable
    `BR_ASSERT(no_deadlock_pop_a, push_vr |-> s_eventually pop_valid)
  end

  // ----------Critical Covers----------
  `BR_COVER_CR(fifo_full_c, push_full, push_clk, push_rst)

  // ----------assert reset again----------
  localparam int ResetLen = NumSyncStages + 2;
  logic [1:0] push_rst_cnt, pop_rst_cnt;
  logic push_rst_flg, pop_rst_flg;
  logic push_rst_d, pop_rst_d;

  `BR_REGNX(push_rst_d, push_rst, push_clk);
  `BR_REGNX(pop_rst_d, pop_rst, pop_clk);
  `BR_REGLX(push_rst_cnt, push_rst_cnt + 1, !push_rst && push_rst_d, push_clk, rst)
  `BR_REGLX(pop_rst_cnt, pop_rst_cnt + 1, !pop_rst && pop_rst_d, pop_clk, rst)
  `BR_REGLX(push_rst_flg, 1, push_rst && !push_rst_d, push_clk, rst)
  `BR_REGLX(pop_rst_flg, 1, pop_rst && !pop_rst_d, pop_clk, rst)

  `BR_ASSUME_CR(push_rst_twice_a, push_rst_cnt <= 2, push_clk, rst)
  `BR_ASSUME_CR(pop_rst_twice_a, pop_rst_cnt <= 2, pop_clk, rst)
  `BR_ASSUME_CR(push_rst_rise_once_a, push_rst_flg |-> !$rose(push_rst), push_clk, rst)
  `BR_ASSUME_CR(pop_rst_rise_once_a, pop_rst_flg |-> !$rose(pop_rst), pop_clk, rst)
  // Don't assert reset until NumSyncStages + 2 cycles after the other side's reset is deasserted
  `BR_ASSUME_CR(no_push_rst_a, !pop_rst |-> !$rose(push_rst) [* ResetLen], push_clk, rst)
  `BR_ASSUME_CR(no_pop_rst_a, !push_rst |-> !$rose(pop_rst) [* ResetLen], pop_clk, rst)
  // Don't deassert reset until NumSyncStages + 2 cycles after the other side's reset is asserted
  `BR_ASSUME_CR(hold_push_rst_a, pop_rst |-> !$fell(push_rst) [* ResetLen], push_clk, rst)
  `BR_ASSUME_CR(hold_pop_rst_a, push_rst |-> !$fell(pop_rst) [* ResetLen], pop_clk, rst)

endmodule : br_cdc_fifo_basic_fpv_monitor
