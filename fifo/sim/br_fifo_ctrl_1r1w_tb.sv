// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`timescale 1ns / 1ps

module br_fifo_ctrl_1r1w_tb;

  // Parameters
  parameter int NumTests = 12;

  parameter int Depth = 13;
  parameter int Width = 8;
  parameter int EnableBypass[NumTests] = '{0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1};
  parameter int RegisterPopOutputs[NumTests] = '{0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1};
  parameter int RamReadLatency[NumTests] = '{1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3};
  localparam int RamAddrWidth = $clog2(Depth);

  // Clock and Reset
  reg clk;
  reg rst;

  logic [NumTests-1:0] start;
  logic [NumTests-1:0] finished;
  logic [NumTests-1:0][31:0] error_count;

  for (genvar i = 0; i < NumTests; i++) begin : gen_tests
    // Push Interface
    wire                        push_ready;
    reg                         push_valid;
    reg   [          Width-1:0] push_data;

    // Pop Interface
    reg                         pop_ready;
    wire                        pop_valid;
    wire  [          Width-1:0] pop_data;

    // Status Outputs
    wire                        empty;
    wire                        full;
    wire  [$clog2(Depth+1)-1:0] items;
    wire  [$clog2(Depth+1)-1:0] slots;

    logic                       ram_wr_valid;
    logic [   RamAddrWidth-1:0] ram_wr_addr;
    logic [          Width-1:0] ram_wr_data;
    logic                       ram_rd_addr_valid;
    logic [   RamAddrWidth-1:0] ram_rd_addr;
    logic                       ram_rd_data_valid;
    logic [          Width-1:0] ram_rd_data;
    logic                       ram_rd_data_valid_next;
    logic [          Width-1:0] ram_rd_data_next;

    // Instantiate the FIFO
    br_fifo_ctrl_1r1w #(
        .Depth(Depth),
        .Width(Width),
        .RegisterPopOutputs(RegisterPopOutputs[i]),
        .EnableBypass(EnableBypass[i]),
        .RamReadLatency(RamReadLatency[i])
    ) dut (
        .clk(clk),
        .rst(rst),
        .push_ready(push_ready),
        .push_valid(push_valid),
        .push_data(push_data),
        .pop_ready(pop_ready),
        .pop_valid(pop_valid),
        .pop_data(pop_data),
        .empty(empty),
        .empty_next(),
        .slots(),
        .slots_next(),
        .full(full),
        .full_next(),
        .items(items),
        .items_next(),
        .ram_wr_valid,
        .ram_wr_addr,
        .ram_wr_data,
        .ram_rd_addr_valid,
        .ram_rd_addr,
        .ram_rd_data_valid,
        .ram_rd_data
    );

    br_ram_flops_1r1w #(
        .Depth(Depth),
        .Width(Width)
    ) br_ram_flops_1r1w (
        .clk,
        .rst,
        .wr_valid     (ram_wr_valid),
        .wr_addr      (ram_wr_addr),
        .wr_data      (ram_wr_data),
        .rd_addr_valid(ram_rd_addr_valid),
        .rd_addr      (ram_rd_addr),
        .rd_data_valid(ram_rd_data_valid_next),
        .rd_data      (ram_rd_data_next)
    );

    // TODO(zhemao): Replace this with the internal retiming controls in br_ram_flops_1r1w
    br_delay_valid #(
        .Width(Width),
        .NumStages(RamReadLatency[i])
    ) br_delay_valid_rd_data (
        .clk,
        .rst,
        .in_valid        (ram_rd_data_valid_next),
        .in              (ram_rd_data_next),
        .out_valid       (ram_rd_data_valid),
        .out             (ram_rd_data),
        .out_valid_stages(),
        .out_stages      ()
    );

    // Hook up the test harness
    br_fifo_test_harness #(
        .Depth(Depth),
        .Width(Width)
    ) br_fifo_test_harness (
        .clk,
        .rst,
        .start      (start[i]),
        .finished   (finished[i]),
        .error_count(error_count[i]),
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data,
        .empty,
        .full,
        .items,
        .slots
    );
  end

  br_test_driver td (
      .clk,
      .rst
  );

  // Test Sequence
  initial begin
    integer timeout;

    start = 0;

    td.reset_dut();

    for (int i = 0; i < NumTests; i++) begin
      $display("Starting test %d", i);

      start[i] = 1'b1;

      timeout  = 5000;
      td.wait_cycles();
      while (timeout > 0 && !finished[i]) td.wait_cycles();

      td.check(timeout > 0, $sformatf("Test %d timed out", i));
      td.check(error_count[i] == 0, $sformatf("Errors in test %d", i));
    end

    td.finish();
  end

endmodule
