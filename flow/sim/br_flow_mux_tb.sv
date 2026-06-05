// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Mux and Burst-Mux Testbench
//
// Test plan: exercise fixed, round-robin, and LRU muxes in unstable and stable
// forms with simultaneous stable requesters, checking selected ready/data and
// registered pop outputs. The burst-mux portion starts a two-beat burst on a
// nonzero flow, asserts a higher-priority requester mid-burst, and checks that
// burst ownership is held until push_last before draining the waiting requester.

module br_flow_mux_tb;
  localparam int NumFlows = 3;
  localparam int Width = 8;

  logic clk;
  logic rst;

  logic [NumFlows-1:0] mux_push_valid;
  logic [NumFlows-1:0][Width-1:0] mux_push_data;
  logic mux_pop_ready;
  logic [NumFlows-1:0] mux_fixed_push_ready;
  logic [NumFlows-1:0] mux_rr_push_ready;
  logic [NumFlows-1:0] mux_lru_push_ready;
  logic mux_fixed_pop_valid_unstable;
  logic mux_rr_pop_valid_unstable;
  logic mux_lru_pop_valid_unstable;
  logic [Width-1:0] mux_fixed_pop_data_unstable;
  logic [Width-1:0] mux_rr_pop_data_unstable;
  logic [Width-1:0] mux_lru_pop_data_unstable;
  logic [NumFlows-1:0] mux_fixed_stable_push_ready;
  logic [NumFlows-1:0] mux_rr_stable_push_ready;
  logic [NumFlows-1:0] mux_lru_stable_push_ready;
  logic mux_fixed_stable_pop_valid;
  logic mux_rr_stable_pop_valid;
  logic mux_lru_stable_pop_valid;
  logic [Width-1:0] mux_fixed_stable_pop_data;
  logic [Width-1:0] mux_rr_stable_pop_data;
  logic [Width-1:0] mux_lru_stable_pop_data;

  logic [NumFlows-1:0] burst_push_valid;
  logic [NumFlows-1:0] burst_push_last;
  logic [NumFlows-1:0][Width-1:0] burst_push_data;
  logic burst_pop_ready;
  logic [NumFlows-1:0] burst_fixed_push_ready;
  logic [NumFlows-1:0] burst_rr_push_ready;
  logic [NumFlows-1:0] burst_lru_push_ready;
  logic burst_fixed_pop_valid_unstable;
  logic burst_rr_pop_valid_unstable;
  logic burst_lru_pop_valid_unstable;
  logic burst_fixed_pop_last_unstable;
  logic burst_rr_pop_last_unstable;
  logic burst_lru_pop_last_unstable;
  logic [Width-1:0] burst_fixed_pop_data_unstable;
  logic [Width-1:0] burst_rr_pop_data_unstable;
  logic [Width-1:0] burst_lru_pop_data_unstable;
  logic [NumFlows-1:0] burst_fixed_stable_push_ready;
  logic [NumFlows-1:0] burst_rr_stable_push_ready;
  logic [NumFlows-1:0] burst_lru_stable_push_ready;
  logic burst_fixed_stable_pop_valid;
  logic burst_rr_stable_pop_valid;
  logic burst_lru_stable_pop_valid;
  logic burst_fixed_stable_pop_last;
  logic burst_rr_stable_pop_last;
  logic burst_lru_stable_pop_last;
  logic [Width-1:0] burst_fixed_stable_pop_data;
  logic [Width-1:0] burst_rr_stable_pop_data;
  logic [Width-1:0] burst_lru_stable_pop_data;

  br_flow_mux_fixed #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_fixed (
      .clk,
      .rst,
      .push_ready(mux_fixed_push_ready),
      .push_valid(mux_push_valid),
      .push_data(mux_push_data),
      .pop_ready(mux_pop_ready),
      .pop_valid_unstable(mux_fixed_pop_valid_unstable),
      .pop_data_unstable(mux_fixed_pop_data_unstable)
  );
  br_flow_mux_rr #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_rr (
      .clk,
      .rst,
      .push_ready(mux_rr_push_ready),
      .push_valid(mux_push_valid),
      .push_data(mux_push_data),
      .pop_ready(mux_pop_ready),
      .pop_valid_unstable(mux_rr_pop_valid_unstable),
      .pop_data_unstable(mux_rr_pop_data_unstable)
  );
  br_flow_mux_lru #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_lru (
      .clk,
      .rst,
      .push_ready(mux_lru_push_ready),
      .push_valid(mux_push_valid),
      .push_data(mux_push_data),
      .pop_ready(mux_pop_ready),
      .pop_valid_unstable(mux_lru_pop_valid_unstable),
      .pop_data_unstable(mux_lru_pop_data_unstable)
  );

  br_flow_mux_fixed_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_fixed_stable (
      .clk,
      .rst,
      .push_ready(mux_fixed_stable_push_ready),
      .push_valid(mux_push_valid),
      .push_data (mux_push_data),
      .pop_ready (mux_pop_ready),
      .pop_valid (mux_fixed_stable_pop_valid),
      .pop_data  (mux_fixed_stable_pop_data)
  );
  br_flow_mux_rr_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_rr_stable (
      .clk,
      .rst,
      .push_ready(mux_rr_stable_push_ready),
      .push_valid(mux_push_valid),
      .push_data (mux_push_data),
      .pop_ready (mux_pop_ready),
      .pop_valid (mux_rr_stable_pop_valid),
      .pop_data  (mux_rr_stable_pop_data)
  );
  br_flow_mux_lru_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_lru_stable (
      .clk,
      .rst,
      .push_ready(mux_lru_stable_push_ready),
      .push_valid(mux_push_valid),
      .push_data (mux_push_data),
      .pop_ready (mux_pop_ready),
      .pop_valid (mux_lru_stable_pop_valid),
      .pop_data  (mux_lru_stable_pop_data)
  );

  br_flow_burst_mux_fixed #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_burst_mux_fixed (
      .clk,
      .rst,
      .push_ready(burst_fixed_push_ready),
      .push_valid(burst_push_valid),
      .push_last(burst_push_last),
      .push_data(burst_push_data),
      .pop_ready(burst_pop_ready),
      .pop_valid_unstable(burst_fixed_pop_valid_unstable),
      .pop_last_unstable(burst_fixed_pop_last_unstable),
      .pop_data_unstable(burst_fixed_pop_data_unstable)
  );
  br_flow_burst_mux_rr #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_burst_mux_rr (
      .clk,
      .rst,
      .push_ready(burst_rr_push_ready),
      .push_valid(burst_push_valid),
      .push_last(burst_push_last),
      .push_data(burst_push_data),
      .pop_ready(burst_pop_ready),
      .pop_valid_unstable(burst_rr_pop_valid_unstable),
      .pop_last_unstable(burst_rr_pop_last_unstable),
      .pop_data_unstable(burst_rr_pop_data_unstable)
  );
  br_flow_burst_mux_lru #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_burst_mux_lru (
      .clk,
      .rst,
      .push_ready(burst_lru_push_ready),
      .push_valid(burst_push_valid),
      .push_last(burst_push_last),
      .push_data(burst_push_data),
      .pop_ready(burst_pop_ready),
      .pop_valid_unstable(burst_lru_pop_valid_unstable),
      .pop_last_unstable(burst_lru_pop_last_unstable),
      .pop_data_unstable(burst_lru_pop_data_unstable)
  );

  br_flow_burst_mux_fixed_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_burst_mux_fixed_stable (
      .clk,
      .rst,
      .push_ready(burst_fixed_stable_push_ready),
      .push_valid(burst_push_valid),
      .push_last (burst_push_last),
      .push_data (burst_push_data),
      .pop_ready (burst_pop_ready),
      .pop_valid (burst_fixed_stable_pop_valid),
      .pop_last  (burst_fixed_stable_pop_last),
      .pop_data  (burst_fixed_stable_pop_data)
  );
  br_flow_burst_mux_rr_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_burst_mux_rr_stable (
      .clk,
      .rst,
      .push_ready(burst_rr_stable_push_ready),
      .push_valid(burst_push_valid),
      .push_last (burst_push_last),
      .push_data (burst_push_data),
      .pop_ready (burst_pop_ready),
      .pop_valid (burst_rr_stable_pop_valid),
      .pop_last  (burst_rr_stable_pop_last),
      .pop_data  (burst_rr_stable_pop_data)
  );
  br_flow_burst_mux_lru_stable #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_burst_mux_lru_stable (
      .clk,
      .rst,
      .push_ready(burst_lru_stable_push_ready),
      .push_valid(burst_push_valid),
      .push_last (burst_push_last),
      .push_data (burst_push_data),
      .pop_ready (burst_pop_ready),
      .pop_valid (burst_lru_stable_pop_valid),
      .pop_last  (burst_lru_stable_pop_last),
      .pop_data  (burst_lru_stable_pop_data)
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_data(input logic [Width-1:0] actual, input logic [Width-1:0] expected,
                            input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got 0x%0h, expected 0x%0h", message, actual, expected);
    end
  endtask

  task automatic check_ready(input logic [NumFlows-1:0] actual, input logic [NumFlows-1:0] expected,
                             input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got %0b, expected %0b", message, actual, expected);
    end
  endtask

  task automatic check_accept(input logic [NumFlows-1:0] ready, input logic [NumFlows-1:0] valid,
                              input logic [NumFlows-1:0] expected, input string message);
    check_ready(ready & valid, expected, message);
  endtask

  initial begin
    mux_push_valid = '0;
    mux_push_data[0] = Width'(8'h10);
    mux_push_data[1] = Width'(8'h20);
    mux_push_data[2] = Width'(8'h30);
    mux_pop_ready = 1'b1;
    burst_push_valid = '0;
    burst_push_last = '0;
    burst_push_data = '0;
    burst_pop_ready = 1'b1;

    td.reset_dut();

    mux_push_valid = 3'b111;
    #1;
    check_ready(mux_fixed_push_ready, 3'b001, "fixed mux initial ready");
    check_ready(mux_rr_push_ready, 3'b001, "rr mux initial ready");
    check_ready(mux_lru_push_ready, 3'b001, "lru mux initial ready");
    check_data(mux_fixed_pop_data_unstable, Width'(8'h10), "fixed mux initial data");
    check_data(mux_rr_pop_data_unstable, Width'(8'h10), "rr mux initial data");
    check_data(mux_lru_pop_data_unstable, Width'(8'h10), "lru mux initial data");

    @(posedge clk);
    #1;
    mux_push_valid[0] = 1'b0;
    #1;
    td.check(mux_fixed_stable_pop_valid && mux_rr_stable_pop_valid && mux_lru_stable_pop_valid,
             "stable muxes should output first transfer");
    check_data(mux_fixed_stable_pop_data, Width'(8'h10), "fixed stable mux first data");
    check_data(mux_rr_stable_pop_data, Width'(8'h10), "rr stable mux first data");
    check_data(mux_lru_stable_pop_data, Width'(8'h10), "lru stable mux first data");
    check_accept(mux_fixed_push_ready, mux_push_valid, 3'b010, "fixed mux second ready");
    check_accept(mux_rr_push_ready, mux_push_valid, 3'b010, "rr mux second ready");
    check_accept(mux_lru_push_ready, mux_push_valid, 3'b010, "lru mux second ready");
    check_data(mux_fixed_pop_data_unstable, Width'(8'h20), "fixed mux second data");
    check_data(mux_rr_pop_data_unstable, Width'(8'h20), "rr mux second data");
    check_data(mux_lru_pop_data_unstable, Width'(8'h20), "lru mux second data");

    @(posedge clk);
    #1;
    td.check(mux_fixed_stable_pop_valid && mux_rr_stable_pop_valid && mux_lru_stable_pop_valid,
             "stable muxes should output second transfer");
    check_data(mux_fixed_stable_pop_data, Width'(8'h20), "fixed stable mux second data");
    check_data(mux_rr_stable_pop_data, Width'(8'h20), "rr stable mux second data");
    check_data(mux_lru_stable_pop_data, Width'(8'h20), "lru stable mux second data");
    mux_push_valid[1] = 1'b0;
    #1;
    check_accept(mux_fixed_push_ready, mux_push_valid, 3'b100, "fixed mux third ready");
    check_accept(mux_rr_push_ready, mux_push_valid, 3'b100, "rr mux third ready");
    check_accept(mux_lru_push_ready, mux_push_valid, 3'b100, "lru mux third ready");
    check_data(mux_fixed_pop_data_unstable, Width'(8'h30), "fixed mux third data");
    check_data(mux_rr_pop_data_unstable, Width'(8'h30), "rr mux third data");
    check_data(mux_lru_pop_data_unstable, Width'(8'h30), "lru mux third data");

    @(posedge clk);
    #1;
    td.check(mux_fixed_stable_pop_valid && mux_rr_stable_pop_valid && mux_lru_stable_pop_valid,
             "stable muxes should output third transfer");
    check_data(mux_fixed_stable_pop_data, Width'(8'h30), "fixed stable mux third data");
    check_data(mux_rr_stable_pop_data, Width'(8'h30), "rr stable mux third data");
    check_data(mux_lru_stable_pop_data, Width'(8'h30), "lru stable mux third data");
    mux_push_valid[2] = 1'b0;

    burst_push_valid = 3'b010;
    burst_push_last = 3'b000;
    burst_push_data[1] = Width'(8'h41);
    #1;
    check_data(burst_fixed_pop_data_unstable, Width'(8'h41), "fixed burst first data");
    check_data(burst_rr_pop_data_unstable, Width'(8'h41), "rr burst first data");
    check_data(burst_lru_pop_data_unstable, Width'(8'h41), "lru burst first data");

    @(posedge clk);
    #1;
    td.check(
        burst_fixed_stable_pop_valid && burst_rr_stable_pop_valid && burst_lru_stable_pop_valid,
        "stable burst muxes should output first beat");
    check_data(burst_fixed_stable_pop_data, Width'(8'h41), "fixed stable burst first data");
    check_data(burst_rr_stable_pop_data, Width'(8'h41), "rr stable burst first data");
    check_data(burst_lru_stable_pop_data, Width'(8'h41), "lru stable burst first data");
    burst_push_valid = 3'b011;
    burst_push_last = 3'b011;
    burst_push_data[0] = Width'(8'h99);
    burst_push_data[1] = Width'(8'h42);
    #1;
    check_data(burst_fixed_pop_data_unstable, Width'(8'h42), "fixed burst holds owner data");
    check_data(burst_rr_pop_data_unstable, Width'(8'h42), "rr burst holds owner data");
    check_data(burst_lru_pop_data_unstable, Width'(8'h42), "lru burst holds owner data");
    td.check(
        burst_fixed_pop_last_unstable && burst_rr_pop_last_unstable && burst_lru_pop_last_unstable,
        "unstable burst muxes should mark second beat last");

    @(posedge clk);
    #1;
    burst_push_valid[1] = 1'b0;
    burst_push_last[1]  = 1'b0;
    #1;
    td.check(
        burst_fixed_stable_pop_valid && burst_rr_stable_pop_valid && burst_lru_stable_pop_valid,
        "stable burst muxes should output held-owner beat");
    check_data(burst_fixed_stable_pop_data, Width'(8'h42), "fixed stable burst held data");
    check_data(burst_rr_stable_pop_data, Width'(8'h42), "rr stable burst held data");
    check_data(burst_lru_stable_pop_data, Width'(8'h42), "lru stable burst held data");
    check_data(burst_fixed_pop_data_unstable, Width'(8'h99), "fixed burst drains waiting data");
    check_data(burst_rr_pop_data_unstable, Width'(8'h99), "rr burst drains waiting data");
    check_data(burst_lru_pop_data_unstable, Width'(8'h99), "lru burst drains waiting data");

    @(posedge clk);
    #1;
    td.check(
        burst_fixed_stable_pop_valid && burst_rr_stable_pop_valid && burst_lru_stable_pop_valid,
        "stable burst muxes should output waiting beat");
    check_data(burst_fixed_stable_pop_data, Width'(8'h99), "fixed stable burst waiting data");
    check_data(burst_rr_stable_pop_data, Width'(8'h99), "rr stable burst waiting data");
    check_data(burst_lru_stable_pop_data, Width'(8'h99), "lru stable burst waiting data");
    burst_push_valid = '0;
    burst_push_last  = '0;

    td.finish();
  end

endmodule
