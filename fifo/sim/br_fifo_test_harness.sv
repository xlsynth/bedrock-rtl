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
//
// Basic test harness for a single FIFO

module br_fifo_test_harness #(
    parameter int Width = 1,
    parameter int Depth = 2,
    parameter int CutThroughLatency = 1,
    parameter int BackpressureLatency = 1
) (
    input  logic        clk,
    input  logic        rst,
    input  logic        start,
    output logic        finished,
    output logic [31:0] error_count,

    input  logic             push_ready,
    output logic             push_valid,
    output logic [Width-1:0] push_data,

    output logic             pop_ready,
    input  logic             pop_valid,
    input  logic [Width-1:0] pop_data,

    input logic                       empty,
    input logic                       full,
    input logic [$clog2(Depth+1)-1:0] items,
    input logic [$clog2(Depth+1)-1:0] slots
);

  // Scoreboard
  reg [Width-1:0] scoreboard[Depth*2];

  initial begin
    integer si;

    push_valid = 1'b0;
    push_data = '0;
    pop_ready = 1'b0;
    finished = 1'b0;
    error_count = '0;

    @(negedge rst);
    @(negedge clk);

    while (!start) @(negedge clk);

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
    repeat (CutThroughLatency) @(negedge clk);
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
    repeat (BackpressureLatency) @(posedge clk);
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
            push_data  = i[Width-1:0];
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

    finished = 1'b1;
  end
endmodule
