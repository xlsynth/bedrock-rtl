// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Mux With Select Testbench
//
// Test plan: route one selected input through the registered output and verify
// ready, valid, data, and drain behavior.

module br_flow_mux_select_tb;
  parameter int NumFlows = 3;
  parameter int Width = 8;

  localparam int SelectWidth = $clog2(NumFlows);

  logic clk;
  logic rst;

  logic [SelectWidth-1:0] select;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  br_flow_mux_select #(
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
    push_valid = '0;
    push_data = '0;
    pop_ready = 1'b1;

    td.reset_dut();

    push_valid[0] = 1'b1;
    push_data[0]  = Width'(8'ha0);
    #1;
    td.check(push_ready == NumFlows'(1), "mux-select ready should target selected flow");

    @(posedge clk);
    #1;
    td.check(pop_valid, "mux-select should register pop valid");
    td.check(pop_data == Width'(8'ha0), "mux-select data mismatch");

    push_valid = '0;
    @(posedge clk);
    #1;
    td.check(!pop_valid, "mux-select should drain after the transfer");

    td.finish();
  end

endmodule
