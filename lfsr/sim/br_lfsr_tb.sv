// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

module br_lfsr_tb;
  parameter int Width = 2;

  logic clk;
  logic rst;
  logic advance;
  logic reinit;
  logic [Width-1:0] initial_state;
  logic [Width-1:0] taps;
  logic out;
  logic [Width-1:0] out_state;

  if (Width == 2) begin : gen_width_2
    assign taps = br_lfsr_taps::TapsWidth2;
  end else if (Width == 3) begin : gen_width_3
    assign taps = br_lfsr_taps::TapsWidth3;
  end else if (Width == 4) begin : gen_width_4
    assign taps = br_lfsr_taps::TapsWidth4;
  end else if (Width == 5) begin : gen_width_5
    assign taps = br_lfsr_taps::TapsWidth5;
  end else if (Width == 6) begin : gen_width_6
    assign taps = br_lfsr_taps::TapsWidth6;
  end else if (Width == 7) begin : gen_width_7
    assign taps = br_lfsr_taps::TapsWidth7;
  end else if (Width == 8) begin : gen_width_8
    assign taps = br_lfsr_taps::TapsWidth8;
  end else if (Width == 9) begin : gen_width_9
    assign taps = br_lfsr_taps::TapsWidth9;
  end else if (Width == 10) begin : gen_width_10
    assign taps = br_lfsr_taps::TapsWidth10;
  end else if (Width == 11) begin : gen_width_11
    assign taps = br_lfsr_taps::TapsWidth11;
  end else if (Width == 12) begin : gen_width_12
    assign taps = br_lfsr_taps::TapsWidth12;
  end else if (Width == 13) begin : gen_width_13
    assign taps = br_lfsr_taps::TapsWidth13;
  end else if (Width == 14) begin : gen_width_14
    assign taps = br_lfsr_taps::TapsWidth14;
  end else if (Width == 15) begin : gen_width_15
    assign taps = br_lfsr_taps::TapsWidth15;
  end else if (Width == 16) begin : gen_width_16
    assign taps = br_lfsr_taps::TapsWidth16;
  end else begin : gen_unsupported_width
    $error("Unsupported width");
  end

  br_lfsr #(
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .reinit,
      .initial_state,
      .taps,
      .advance,
      .out,
      .out_state
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    initial_state = Width'(1'b1);
    reinit = 0;
    advance = 0;

    // Apply reset
    td.reset_dut();

    // Measure period
    begin
      int ones_count;
      int zeros_count;
      int period;

      zeros_count = out == 0;
      ones_count = out == 1;
      period = 1;

      advance = 1;
      td.wait_cycles();

      while (out_state != initial_state) begin
        zeros_count += (out == 0);
        ones_count += (out == 1);
        period++;

        // Stall for random cycles
        advance = 0;
        td.wait_cycles($urandom() % 3);

        advance = 1;
        td.wait_cycles();
      end

      td.check_integer(period, 2 ** Width - 1, "Period mismatch");
      td.check_integer(ones_count, zeros_count + 1, "Ones and zeros count mismatch");
    end

    td.finish();
  end
endmodule
