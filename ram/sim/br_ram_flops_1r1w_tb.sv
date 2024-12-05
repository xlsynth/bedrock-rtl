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
    parameter int Depth = 16,
    parameter int Width = 8,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1,
    parameter int AddressDepthStages = 0,
    parameter int ReadDataDepthStages = 0,
    parameter int ReadDataWidthStages = 0,
    parameter bit TileEnableBypass = 0,
    parameter bit EnableMemReset = 0,
    parameter bit EnableMock = 0
) ();

  // Clock and Reset
  logic clk;
  logic rst;

  initial clk = 0;
  always #5 clk = ~clk;  // 100 MHz clock

  localparam int AddressWidth = $clog2(Depth);
  localparam int ReadLatency = AddressDepthStages + ReadDataDepthStages + ReadDataWidthStages;

  // DUT signals
  logic                    wr_valid;
  logic [AddressWidth-1:0] wr_addr;
  logic [       Width-1:0] wr_data;
  logic                    rd_addr_valid;
  logic [AddressWidth-1:0] rd_addr;
  logic                    rd_data_valid;
  logic [       Width-1:0] rd_data;

  // DUT instantiation
  if (EnableMock) begin : gen_mock
    br_ram_flops_1r1w_mock #(
        .Depth(Depth),
        .Width(Width),
        .DepthTiles(DepthTiles),
        .WidthTiles(WidthTiles),
        .AddressDepthStages(AddressDepthStages),
        .ReadDataDepthStages(ReadDataDepthStages),
        .ReadDataWidthStages(ReadDataWidthStages),
        .TileEnableBypass(TileEnableBypass),
        .EnableMemReset(EnableMemReset)
    ) dut (
        .wr_clk(clk),
        .wr_rst(rst),
        .wr_valid,
        .wr_addr,
        .wr_data,
        .rd_clk(clk),
        .rd_rst(rst),
        .rd_addr_valid,
        .rd_addr,
        .rd_data_valid,
        .rd_data
    );
  end else begin : gen_real
    br_ram_flops_1r1w #(
        .Depth(Depth),
        .Width(Width),
        .DepthTiles(DepthTiles),
        .WidthTiles(WidthTiles),
        .AddressDepthStages(AddressDepthStages),
        .ReadDataDepthStages(ReadDataDepthStages),
        .ReadDataWidthStages(ReadDataWidthStages),
        .TileEnableBypass(TileEnableBypass),
        .EnableMemReset(EnableMemReset)
    ) dut (
        .wr_clk(clk),
        .wr_rst(rst),
        .wr_valid,
        .wr_addr,
        .wr_data,
        .rd_clk(clk),
        .rd_rst(rst),
        .rd_addr_valid,
        .rd_addr,
        .rd_data_valid,
        .rd_data
    );
  end

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

    $display("Phase 1: Sequential write to every address");
    for (int i = 0; i < Depth; i++) begin
      @(negedge clk);
      wr_valid = 1;
      wr_addr = i;
      wr_data = $urandom();
      expected_memory[i] = wr_data;
    end
    @(negedge clk);
    wr_valid = 0;

    // Wait for potential pipeline delays
    #100;

    $display("Phase 2: Sequential read from every address to check initial writes");
    for (int i = 0; i < Depth; i++) begin
      @(negedge clk);
      rd_addr_valid = 1;
      rd_addr = i;
      // TODO(mgottscho): BUG: this does not account for read latency and pipelining
      @(negedge clk);
      if (rd_data_valid) begin
        @(negedge clk);
        if (rd_data !== expected_memory[i]) begin
          $display("ERROR: Mismatch at address %0d. Expected 0x%0h, got 0x%0h", i,
                   expected_memory[i], rd_data);
          error_count++;
        end
      end
    end
    rd_addr_valid = 0;

    $display("Phase 3: Write-only stress phase");
    for (int k = 0; k < 100; k++) begin
      @(negedge clk);
      wr_valid = 1;
      wr_addr = $urandom_range(0, Depth - 1);  // Random address
      wr_data = $urandom();
      expected_memory[wr_addr] = wr_data;  // Update expected memory
    end
    @(negedge clk);
    wr_valid = 0;

    // Wait for potential pipeline delays
    #100;

    $display("Phase 4: Read-only stress phase");
    for (int k = 0; k < 100; k++) begin
      @(negedge clk);
      rd_addr_valid = 1;
      rd_addr = $urandom_range(0, Depth - 1);  // Random address
      // TODO(mgottscho): BUG: this does not account for pipelined reads
      #ReadLatency;  // Wait for read latency delay

      // Check result
      if (rd_data_valid) begin
        @(negedge clk);
        if (rd_data !== expected_memory[rd_addr]) begin
          $display("ERROR: Mismatch at address %0d during random read. Expected 0x%0h, got 0x%0h",
                   rd_addr, expected_memory[rd_addr], rd_data);
          error_count++;
        end
      end
    end
    @(negedge clk);
    rd_addr_valid = 0;

    // Wait for potential pipeline delays
    #100;

    $display("Phase 5: Write + Read stress phase");
    for (int k = 0; k < 200; k++) begin
      @(negedge clk);
      wr_valid = $urandom_range(0, 1);  // Random decision to write
      wr_addr = $urandom_range(0, Depth - 1);
      wr_data = $urandom();

      rd_addr_valid = $urandom_range(0, 1);  // Random decision to read
      rd_addr = $urandom_range(0, Depth - 1);

      // For simplicity in this unit test, don't scoreboard write data or check read data.
      // TODO(mgottscho): Do so.
    end

    @(negedge clk);
    wr_valid = 0;
    rd_addr_valid = 0;

    // Final check
    if (error_count == 0) begin
      $display("TEST PASSED");
    end else begin
      $display("TEST FAILED with %0d errors", error_count);
    end

    $finish;
  end
endmodule
