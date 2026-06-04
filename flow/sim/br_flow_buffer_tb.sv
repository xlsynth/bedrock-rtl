// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Buffer Testbench
//
// Test plan: exercise legal shallow and FIFO-backed configurations with
// randomized ready/valid traffic and output backpressure.

module br_flow_buffer_tb #(
    parameter int Depth = 2,
    parameter int Width = 8,
    parameter bit RegisterPushOutputs = 1,
    parameter bit RegisterPopOutputs = 1,
    parameter int NumRandomValues = 64
);
  logic clk;
  logic rst;

  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  logic driver_done;
  logic sink_done;
  logic sink_error;

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
  ) driver (
      .clk,
      .rst,
      .test_data('0),
      .pop_ready(push_ready),
      .pop_valid(push_valid),
      .pop_data(push_data),
      .done(driver_done)
  );

  br_flow_test_sink #(
      .Width(Width),
      .NumValues(NumRandomValues),
      .Rate(0.41),
      .InitialDelay(5),
      .Seed(404)
  ) sink (
      .clk,
      .rst,
      .expected_data('0),
      .push_ready(pop_ready),
      .push_valid(pop_valid),
      .push_data(pop_data),
      .done(sink_done),
      .error(sink_error)
  );

  initial begin
    int timeout;

    td.reset_dut();

    timeout = (NumRandomValues * 40) + 200;
    while (!(driver_done && sink_done) && timeout > 0) begin
      td.wait_cycles();
      timeout--;
    end

    td.check(timeout > 0, "random ready/valid flow timed out");
    td.check(!sink_error, "random ready/valid sink reported an error");

    td.finish();
  end

endmodule : br_flow_buffer_tb
