// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Buffer Testbench
//
// Test plan: exercise legal shallow and FIFO-backed configurations with
// single transfers, output backpressure, and randomized ready/valid traffic.

module br_flow_buffer_tb #(
    parameter int Depth = 2,
    parameter int Width = 8,
    parameter bit RegisterPushOutputs = 1,
    parameter bit RegisterPopOutputs = 1,
    parameter int NumRandomValues = 64
);
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

  br_flow_buffer #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterPopOutputs(RegisterPopOutputs)
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

  br_test_driver td (
      .clk,
      .rst
  );

  br_flow_test_driver #(
      .Width(Width),
      .NumValues(NumRandomValues),
      .Rate(0.73),
      .InitialDelay(3),
      .Seed(303)
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
      .Seed(404)
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
    return Depth == 0 || !RegisterPopOutputs;
  endfunction

  task automatic init_manual_signals();
    use_random_driver = 1'b0;
    manual_push_valid = 1'b0;
    manual_push_data  = '0;
    manual_pop_ready  = 1'b0;
  endtask

  task automatic check_pop(input logic [Width-1:0] expected);
    td.check(pop_valid, "pop_valid is not asserted");
    td.check(pop_data === expected, "pop_data does not match expected data");
  endtask

  task automatic check_after_reset();
    #1;
    td.check(!pop_valid, "pop_valid should be deasserted after reset");
    if (Depth > 0) begin
      td.check(push_ready, "push_ready should be asserted after reset");
    end
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
      td.check(!pop_valid, "pop_valid should be registered for this configuration");
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

    if (Depth == 0) begin
      td.wait_cycles(2);
      #1;
      check_pop(data);
      manual_pop_ready = 1'b1;
      @(posedge clk);
    end else begin
      while (!push_ready) begin
        td.wait_cycles();
      end
      @(posedge clk);
    end

    @(negedge clk);
    manual_push_valid = 1'b0;
    manual_push_data  = '0;

    if (Depth > 0) begin
      td.wait_cycles(2);
      #1;
      check_pop(data);
      manual_pop_ready = 1'b1;
      @(posedge clk);
    end

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
    if (Depth < 0) begin
      $fatal(1, "Depth must be at least 0");
    end
    if (Width < 1) begin
      $fatal(1, "Width must be at least 1");
    end
    if (Depth == 1 && RegisterPushOutputs && RegisterPopOutputs) begin
      $fatal(1, "Depth 1 cannot register both push and pop outputs");
    end
    if (Depth >= 3 && !RegisterPushOutputs) begin
      $fatal(1, "Depth >= 3 requires registered push outputs");
    end

    init_manual_signals();
    td.reset_dut();
    check_after_reset();

    check_single_transfer(Width'('h5a));
    check_backpressure_hold(Width'('ha5));
    run_random_flow();

    td.finish();
  end

endmodule : br_flow_buffer_tb
