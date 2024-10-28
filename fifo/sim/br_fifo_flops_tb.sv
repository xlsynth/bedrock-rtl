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

// This unit test doesn't yet scoreboard the values (so you currently need to
// eyeball the text output to make sure it looks right).
// TODO(mgottscho): scoreboard

`timescale 1ns / 1ps

module br_fifo_flops_tb;

  // Parameters
  parameter int Depth = 13;
  parameter int BitWidth = 8;

  // Clock and Reset
  reg clk;
  reg rst;

  // Push Interface
  wire push_ready;
  reg push_valid;
  reg [BitWidth-1:0] push_data;

  // Pop Interface
  reg pop_ready;
  wire pop_valid;
  wire [BitWidth-1:0] pop_data;

  // Status Outputs
  wire empty;
  wire full;
  wire [$clog2(Depth+1)-1:0] items;

  // Scoreboard
  reg [BitWidth-1:0] scoreboard[Depth*2];

  // Error Counter
  integer error_count;

  // Instantiate the FIFO
  br_fifo_flops #(
      .Depth(Depth),
      .BitWidth(BitWidth),
      .EnableBypass(0)
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
      .items_next()
  );

`ifdef DUMP_WAVES
  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
`endif

  // Clock Generation: 10ns period
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test Sequence
  initial begin
    integer si;
    // Initialize signals
    rst = 1;
    push_valid = 0;
    push_data = 0;
    pop_ready = 0;
    error_count = 0;

    // Apply Reset
    #20;
    rst = 0;
    #10;

    // Test 1: Fill the FIFO completely
    $display("Test 1: Filling the FIFO completely...");
    si = 0;
    repeat (Depth) begin
      @(negedge clk);
      if (push_ready) begin
        push_valid = 1;
        push_data = $urandom;
        scoreboard[si] = push_data;
        $display("Pushed data: %0h | Items: %0d | Full: %b", push_data, items, full);
      end else begin
        push_valid = 0;
        $error("FIFO is full. Cannot push data.");
        error_count += 1;
      end
      si += 1;
    end
    @(negedge clk);
    push_valid = 0;

    // Check if FIFO is full
    @(negedge clk);
    if (full && !empty && (items == Depth))
      $display("FIFO is full as expected with %0d items.", items);
    else begin
      $error("Error: FIFO full state is not as expected.");
      error_count += 1;
    end

    // Test 2: Attempt to push into a full FIFO
    @(negedge clk);
    push_valid = 1;
    push_data  = $urandom;
    @(negedge clk);
    if (!push_ready) $display("Correctly prevented pushing into a full FIFO.");
    else begin
      $error("Error: Allowed pushing into a full FIFO.");
      error_count += 1;
    end
    push_valid = 0;

    // Test 3: Pop all items from the FIFO
    $display("Test 3: Popping all items from the FIFO...");
    si = 0;
    pop_ready = 1;
    while (!empty) begin
      @(posedge clk);
      if (pop_valid) begin
        $display("Popped data: %0h | Items: %0d | Empty: %b", pop_data, items, empty);
        if (pop_data != scoreboard[si]) begin
          $error("Pop data mismatch! expect=%0h got=%0h", scoreboard[si], pop_data);
          error_count += 1;
        end
      end
      si += 1;
    end
    @(negedge clk);
    pop_ready = 0;

    // Check if FIFO is empty
    @(posedge clk);
    if (empty && !full && (items == 0))
      $display("FIFO is empty as expected with %0d items.", items);
    else begin
      $error("Error: FIFO empty state is not as expected.");
      error_count += 1;
    end

    // Test 4: Attempt to pop from an empty FIFO
    @(negedge clk);
    pop_ready = 1;
    @(posedge clk);
    if (!pop_valid) $display("Correctly prevented popping from an empty FIFO.");
    else begin
      $error("Error: Allowed popping from an empty FIFO.");
      error_count += 1;
    end
    pop_ready = 0;

    // Test 5: Interleaved push and pop operations
    $display("Test 5: Interleaved push and pop operations...");
    fork
      // Push process
      begin
        integer i;
        for (i = 0; i < Depth * 2; i = i + 1) begin
          @(negedge clk);
          if (push_ready) begin
            push_valid = 1;
            push_data  = i[BitWidth-1:0];
            @(posedge clk);
            scoreboard[i] = push_data;
            $display("Pushed data: %0h | Items: %0d", push_data, items);
          end else begin
            push_valid = 0;
            @(posedge clk);
            $error("Cannot push data. FIFO Full.");
            error_count += 1;
          end
        end
        @(negedge clk);
        push_valid = 0;
      end
      // Pop process
      begin
        integer j;
        @(posedge pop_valid);
        for (j = 0; j < Depth * 2; j = j + 1) begin
          @(negedge clk);
          if (pop_valid) begin
            pop_ready = 1;
            @(posedge clk);
            $display("Popped data: %0h | Items: %0d", pop_data, items);
            if (pop_data != scoreboard[j]) begin
              $error("Pop data mismatch! expect=%0h got=%0h", scoreboard[j], pop_data);
              error_count += 1;
            end
          end else begin
            pop_ready = 0;
            @(posedge clk);
            $error("Cannot pop data. FIFO Empty.");
            error_count += 1;
          end
        end
        @(negedge clk);
        pop_ready = 0;
      end
    join

    // Final check
    @(negedge clk);
    if (empty && (items == 0)) $display("FIFO successfully emptied after interleaved operations.");
    else begin
      $error("Error: FIFO state incorrect after interleaved operations.");
      error_count += 1;
    end

    if (error_count == 0) $display("TEST PASSED");
    else $display("TEST FAILED with %0d errors", error_count);
    $finish;
  end

endmodule
