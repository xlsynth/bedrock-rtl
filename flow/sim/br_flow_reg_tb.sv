// SPDX-License-Identifier: Apache-2.0

module br_flow_reg_tb #(
    parameter int Width = 8,
    parameter int NumRandomValues = 64,
    parameter int RegVariant = 0
);
  localparam int RegVariantFwd = 0;
  localparam int RegVariantRev = 1;
  localparam int RegVariantNone = 2;
  localparam int RegVariantBoth = 3;

  logic clk;
  logic rst;

  logic use_random_driver;
  logic manual_push_valid;
  logic [Width-1:0] manual_push_data;
  logic manual_pop_ready;
  logic random_push_valid;
  logic [Width-1:0] random_push_data;
  logic random_pop_ready;

  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  logic random_driver_done;
  logic random_sink_done;
  logic random_sink_error;
  logic helper_rst;

  assign push_valid = use_random_driver ? random_push_valid : manual_push_valid;
  assign push_data  = use_random_driver ? random_push_data : manual_push_data;
  assign pop_ready  = use_random_driver ? random_pop_ready : manual_pop_ready;
  assign helper_rst = rst || !use_random_driver;

  if (RegVariant == RegVariantFwd) begin : gen_dut_fwd
    br_flow_reg_fwd #(
        .Width(Width)
    ) dut (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end else if (RegVariant == RegVariantRev) begin : gen_dut_rev
    br_flow_reg_rev #(
        .Width(Width)
    ) dut (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end else if (RegVariant == RegVariantNone) begin : gen_dut_none
    br_flow_reg_none #(
        .Width(Width)
    ) dut (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end else begin : gen_dut_both
    br_flow_reg_both #(
        .Width(Width)
    ) dut (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end

  br_test_driver td (
      .clk,
      .rst
  );

  br_flow_test_driver #(
      .Width(Width),
      .NumValues(NumRandomValues),
      .Rate(0.73),
      .InitialDelay(3),
      .Seed(101)
  ) random_driver (
      .clk,
      .rst(helper_rst),
      .test_data('0),
      .pop_ready(push_ready),
      .pop_valid(random_push_valid),
      .pop_data(random_push_data),
      .done(random_driver_done)
  );

  br_flow_test_sink #(
      .Width(Width),
      .NumValues(NumRandomValues),
      .Rate(0.41),
      .InitialDelay(5),
      .Seed(202)
  ) random_sink (
      .clk,
      .rst(helper_rst),
      .expected_data('0),
      .push_ready(random_pop_ready),
      .push_valid(pop_valid),
      .push_data(pop_data),
      .done(random_sink_done),
      .error(random_sink_error)
  );

  function automatic bit has_zero_cycle_cutthrough();
    return RegVariant == RegVariantRev || RegVariant == RegVariantNone;
  endfunction

  task automatic check_pop(input logic [Width-1:0] expected);
    td.check(pop_valid, "pop_valid is not asserted");
    td.check(pop_data === expected, "pop_data does not match expected data");
  endtask

  task automatic init_manual_signals();
    use_random_driver = 1'b0;
    manual_push_valid = 1'b0;
    manual_push_data  = '0;
    manual_pop_ready  = 1'b0;
  endtask

  task automatic check_after_reset();
    #1;
    td.check(push_ready, "push_ready should be asserted after reset");
    td.check(!pop_valid, "pop_valid should be deasserted after reset");
  endtask

  task automatic check_single_transfer(input logic [Width-1:0] data);
    manual_pop_ready  = 1'b1;
    manual_push_data  = data;
    manual_push_valid = 1'b1;
    #1;

    td.check(push_ready, "push_ready should accept an empty single transfer");
    if (has_zero_cycle_cutthrough()) begin
      check_pop(data);
    end else begin
      td.check(!pop_valid, "pop_valid should be registered for this variant");
    end

    @(posedge clk);
    #1;
    check_pop(data);

    @(negedge clk);
    manual_push_valid = 1'b0;
    manual_push_data  = '0;

    @(posedge clk);
    #1;
    td.check(!pop_valid, "single transfer did not drain");

    @(negedge clk);
    manual_pop_ready = 1'b0;
  endtask

  task automatic check_backpressure_hold(input logic [Width-1:0] data);
    manual_pop_ready  = 1'b0;
    manual_push_data  = data;
    manual_push_valid = 1'b1;
    #1;

    if (has_zero_cycle_cutthrough()) begin
      check_pop(data);
    end

    @(posedge clk);
    #1;
    check_pop(data);

    @(negedge clk);
    manual_push_valid = 1'b0;
    manual_push_data  = '1;
    #1;
    check_pop(data);

    td.wait_cycles(2);
    check_pop(data);

    manual_pop_ready = 1'b1;
    @(posedge clk);
    #1;
    td.check(!pop_valid, "backpressured transfer did not drain");

    @(negedge clk);
    manual_pop_ready = 1'b0;
  endtask

  task automatic run_random_flow();
    int timeout;

    init_manual_signals();
    td.reset_dut();
    check_after_reset();

    @(negedge clk);
    use_random_driver = 1'b1;
    timeout = (NumRandomValues * 40) + 200;
    while (!(random_driver_done && random_sink_done) && timeout > 0) begin
      td.wait_cycles();
      timeout--;
    end

    td.check(timeout > 0, "random ready/valid flow timed out");
    td.check(!random_sink_error, "random ready/valid sink reported an error");

    @(negedge clk);
    init_manual_signals();
  endtask

  initial begin
    if (Width < 1) begin
      $fatal(1, "Width must be at least 1");
    end
    if (RegVariant < RegVariantFwd || RegVariant > RegVariantBoth) begin
      $fatal(1, "Unsupported RegVariant %0d", RegVariant);
    end

    init_manual_signals();
    td.reset_dut();
    check_after_reset();

    check_single_transfer(Width'('h5a));
    check_backpressure_hold(Width'('ha5));
    run_random_flow();

    td.finish();
  end

endmodule : br_flow_reg_tb

module br_flow_reg_fwd_tb #(
    parameter int Width = 8,
    parameter int NumRandomValues = 64
);
  br_flow_reg_tb #(
      .Width(Width),
      .NumRandomValues(NumRandomValues),
      .RegVariant(0)
  ) tb ();
endmodule : br_flow_reg_fwd_tb

module br_flow_reg_rev_tb #(
    parameter int Width = 8,
    parameter int NumRandomValues = 64
);
  br_flow_reg_tb #(
      .Width(Width),
      .NumRandomValues(NumRandomValues),
      .RegVariant(1)
  ) tb ();
endmodule : br_flow_reg_rev_tb

module br_flow_reg_none_tb #(
    parameter int Width = 8,
    parameter int NumRandomValues = 64
);
  br_flow_reg_tb #(
      .Width(Width),
      .NumRandomValues(NumRandomValues),
      .RegVariant(2)
  ) tb ();
endmodule : br_flow_reg_none_tb

module br_flow_reg_both_tb #(
    parameter int Width = 8,
    parameter int NumRandomValues = 64
);
  br_flow_reg_tb #(
      .Width(Width),
      .NumRandomValues(NumRandomValues),
      .RegVariant(3)
  ) tb ();
endmodule : br_flow_reg_both_tb
