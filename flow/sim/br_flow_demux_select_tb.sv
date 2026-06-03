// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Demux With Select Testbench
//
// Test plan: route one input through a selected registered output and verify
// ready, valid, data, and drain behavior.

module br_flow_demux_select_tb;
  parameter int NumFlows = 3;
  parameter int Width = 8;

  localparam int SelectWidth = $clog2(NumFlows);

  logic clk;
  logic rst;

  logic [SelectWidth-1:0] select;
  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;
  logic [NumFlows-1:0] pop_ready;
  logic [NumFlows-1:0] pop_valid;
  logic [NumFlows-1:0][Width-1:0] pop_data;

  br_flow_demux_select #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .select,
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

  initial begin
    select = '0;
    push_valid = 1'b0;
    push_data = '0;
    pop_ready = '1;

    td.reset_dut();

    select = SelectWidth'(1);
    push_valid = 1'b1;
    push_data = Width'(8'h66);
    #1;
    td.check(push_ready, "demux-select should be ready when selected pop is ready");

    @(posedge clk);
    #1;
    td.check(pop_valid == NumFlows'(1 << 1), "demux-select valid route mismatch");
    td.check(pop_data[1] == Width'(8'h66), "demux-select data mismatch");

    push_valid = 1'b0;
    @(posedge clk);
    #1;
    td.check(pop_valid == '0, "demux-select should drain after the transfer");

    td.finish();
  end

endmodule
