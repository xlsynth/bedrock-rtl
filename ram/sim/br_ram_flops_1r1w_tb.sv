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

module br_ram_flops_1r1w_tb #(
    parameter int Depth               = 16,  // Default depth, adjustable
    parameter int Width               = 8,   // Default width, adjustable
    parameter int DepthTiles          = 1,   // Number of tiles along the depth dimension
    parameter int WidthTiles          = 1,   // Number of tiles along the width dimension
    parameter int AddressDepthStages  = 0,   // Pipeline stages for address depth
    parameter int ReadDataDepthStages = 0,   // Pipeline stages for read depth
    parameter int ReadDataWidthStages = 0    // Pipeline stages for read width
) ();

  // Clock and Reset
  logic clk;
  logic rst;

  initial clk = 0;
  always #5 clk = ~clk;  // 100 MHz clock

  localparam int AddressWidth = $clog2(Depth);

  // DUT signals
  logic                    wr_valid;
  logic [AddressWidth-1:0] wr_addr;
  logic [       Width-1:0] wr_data;
  logic                    rd_addr_valid;
  logic [AddressWidth-1:0] rd_addr;
  logic                    rd_data_valid;
  logic [       Width-1:0] rd_data;

  // DUT instantiation
  br_ram_flops_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles),
      .AddressDepthStages(AddressDepthStages),
      .ReadDataDepthStages(ReadDataDepthStages),
      .ReadDataWidthStages(ReadDataWidthStages)
  ) dut (
      .clk,
      .rst,
      .wr_valid,
      .wr_addr,
      .wr_data,
      .rd_addr_valid,
      .rd_addr,
      .rd_data_valid,
      .rd_data
  );

  // Scoreboard memory to track expected values
  logic [Width-1:0] expected_memory[Depth];
  int error_count = 0;

  initial begin
    rst = 1;
    wr_valid = 0;
    rd_addr_valid = 0;
    wr_addr = '0;
    wr_data = '0;
    #20 rst = 0;  // Release reset after 20ns

    // Phase 1: Write each address with unique data
    for (int i = 0; i < Depth; i++) begin
      @(negedge clk);
      wr_valid = 1;
      wr_addr = i;
      wr_data = $urandom();  // Random data for each address
      expected_memory[i] = wr_data;  // Track data in the expected memory
    end

    // Deactivate write after completing the loop
    @(negedge clk);
    wr_valid = 0;

    // Wait for any pipeline latency to stabilize (e.g., 100 cycles)
    #100;

    // Phase 2: Read each address sequentially and verify data
    for (int i = 0; i < Depth; i++) begin
      @(negedge clk);
      rd_addr_valid = 1;
      rd_addr = i;
      @(posedge clk);  // Wait for DUT to process the read

      if (rd_data_valid) begin
        @(negedge clk);
        if (rd_data !== expected_memory[i]) begin
          $display("ERROR: Mismatch at address %0d. Expected 0x%0h, got 0x%0h", i,
                   expected_memory[i], rd_data);
          error_count++;
        end
      end
    end

    // Completion and Result Check
    if (error_count == 0) begin
      $display("TEST PASSED");
    end else begin
      $display("TEST FAILED with %0d errors", error_count);
    end

    $finish;
  end

endmodule
