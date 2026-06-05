// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Mux With Select Testbench
//
// Test plan: route every selected input through the registered output and
// verify ready, valid, data, one-cycle latency, and drain behavior.

module br_flow_mux_select_tb;
  parameter int NumFlows = 3;
  parameter int Width = 8;

  localparam int SelectWidth = (NumFlows > 1) ? $clog2(NumFlows) : 1;

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

  task automatic check_route(input int route);
    @(negedge clk);
    select = SelectWidth'(route);
    push_valid[route] = 1'b1;
    push_data[route] = Width'(route + 8'ha0);
    #1;
    td.check(push_ready == NumFlows'(1 << route), "mux-select ready should target selected flow");
    td.check(!pop_valid, "mux-select should add one cycle of latency");

    @(posedge clk);
    #1;
    td.check(pop_valid, "mux-select should register pop valid");
    td.check(pop_data == Width'(route + 8'ha0), "mux-select data mismatch");

    @(negedge clk);
    push_valid = '0;
    push_data  = '0;
    @(posedge clk);
    #1;
    td.check(!pop_valid, "mux-select should drain after the transfer");
  endtask

  initial begin
    select = '0;
    push_valid = '0;
    push_data = '0;
    pop_ready = 1'b1;

    td.reset_dut();

    for (int route = 0; route < NumFlows; route++) begin
      check_route(route);
    end

    td.finish();
  end

endmodule : br_flow_mux_select_tb
