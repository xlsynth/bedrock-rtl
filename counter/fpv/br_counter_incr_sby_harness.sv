// SPDX-License-Identifier: Apache-2.0

// SymbiYosys harness for the Bedrock-RTL incrementing counter.

module br_counter_incr_sby_harness #(
    parameter int MaxValueWidth = 32,
    parameter int MaxIncrementWidth = 32,
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    parameter logic [MaxIncrementWidth-1:0] MaxIncrement = 1,
    parameter bit EnableReinitAndIncr = 1,
    parameter bit EnableSaturate = 0,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxIncrementP1Width = MaxIncrementWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int IncrementWidth = $clog2(MaxIncrementP1Width'(MaxIncrement) + 1)
) (
    input logic clk,
    input logic rst,
    input logic reinit,
    input logic [ValueWidth-1:0] initial_value,
    input logic incr_valid,
    input logic [IncrementWidth-1:0] incr
);

  logic [ValueWidth-1:0] value;
  logic [ValueWidth-1:0] value_next;

  br_counter_incr #(
      .MaxValueWidth(MaxValueWidth),
      .MaxIncrementWidth(MaxIncrementWidth),
      .MaxValue(MaxValue),
      .MaxIncrement(MaxIncrement),
      .EnableReinitAndIncr(EnableReinitAndIncr),
      .EnableSaturate(EnableSaturate),
      .EnableAssertFinalNotValid(0)
  ) dut (
      .clk,
      .rst,
      .reinit,
      .initial_value,
      .incr_valid,
      .incr,
      .value,
      .value_next
  );

  function automatic logic [ValueWidth-1:0] adjust(input logic [ValueWidth-1:0] base,
                                                   input logic [IncrementWidth-1:0] increment);
    logic [ValueWidth:0] sum;

    sum = {1'b0, base} + increment;
    if (sum > MaxValue) begin
      adjust = EnableSaturate ? ValueWidth'(MaxValue) : sum - MaxValue - 1'b1;
    end else begin
      adjust = sum[ValueWidth-1:0];
    end
  endfunction

  logic [ValueWidth-1:0] fv_counter;
  logic [ValueWidth-1:0] fv_expected_next;
  logic [IncrementWidth-1:0] fv_increment;

  always_comb begin
    fv_increment = incr_valid ? incr : '0;
    if (reinit) begin
      fv_expected_next = EnableReinitAndIncr ? adjust(initial_value, fv_increment) : initial_value;
    end else begin
      fv_expected_next = adjust(value, fv_increment);
    end
  end

  logic fv_past_valid = 1'b0;

  always @(posedge clk) begin
    fv_past_valid <= 1'b1;
    assume (rst == !fv_past_valid);
    assume (initial_value <= MaxValue);
    assume (incr <= MaxIncrement);

    if (rst) begin
      fv_counter <= initial_value;
    end else begin
      assert (value == fv_counter);
      assert (value <= MaxValue);
      assert (value_next <= MaxValue);
      assert (value_next == fv_expected_next);

      fv_counter <= fv_expected_next;

      cover (reinit && incr_valid && incr > 0);
      cover ({1'b0, fv_counter} + fv_increment > MaxValue);
    end
  end

endmodule : br_counter_incr_sby_harness
