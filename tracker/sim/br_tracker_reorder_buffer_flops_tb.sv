// Copyright 2024-2025 The Bedrock-RTL Authors
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

module br_tracker_reorder_buffer_flops_tb;
  // We'll test with 4 entries
  parameter int NumEntries = 4;
  localparam int EntryIdWidth = $clog2(NumEntries);
  localparam int DataWidth = 8;

  // Testbench signals
  logic clk;
  logic rst;

  // DUT I/O
  logic alloc_ready;
  logic alloc_valid;
  logic [EntryIdWidth-1:0] alloc_entry_id;

  logic unordered_resp_push_valid;
  logic [EntryIdWidth-1:0] unordered_resp_push_entry_id;
  logic [DataWidth-1:0]    unordered_resp_push_data;

  logic reordered_resp_pop_ready;
  logic reordered_resp_pop_valid;
  logic [DataWidth-1:0]    reordered_resp_pop_data;

  // For capturing the allocated IDs (in the order they were allocated)
  logic [EntryIdWidth-1:0] allocated_ids [NumEntries];
  // For assigning unique data to each entry ID
  logic [DataWidth-1:0]    entry_data [NumEntries];

  // Instantiate the DUT
  br_tracker_reorder_buffer_flops #(
      .NumEntries(NumEntries),
      .EntryIdWidth(EntryIdWidth),
      .DataWidth(DataWidth),
      .EnableAssertFinalNotDeallocValid(1)
  ) dut (
      .clk           (clk),
      .rst           (rst),
      .alloc_ready   (alloc_ready),
      .alloc_valid   (alloc_valid),
      .alloc_entry_id(alloc_entry_id),

      .unordered_resp_push_valid   (unordered_resp_push_valid),
      .unordered_resp_push_entry_id(unordered_resp_push_entry_id),
      .unordered_resp_push_data    (unordered_resp_push_data),

      .reordered_resp_pop_ready(reordered_resp_pop_ready),
      .reordered_resp_pop_valid(reordered_resp_pop_valid),
      .reordered_resp_pop_data (reordered_resp_pop_data),

      .free_entry_count(),
      .allocated_entry_count()
  );

  // Clock generation
  always #5 clk = ~clk;

  // Reorder the entries to be deallocated
  int reorder[NumEntries] = '{2, 0, 3, 1};

  // Test procedure
  initial begin
    // Initialize signals
    clk                          = 1'b0;
    rst                          = 1'b1;
    alloc_ready                  = 1'b0;
    unordered_resp_push_valid    = 1'b0;
    unordered_resp_push_entry_id = '0;
    unordered_resp_push_data     = '0;
    reordered_resp_pop_ready     = 1'b0;

    // Prepare some known unique data patterns for each entry
    for (int i = 0; i < NumEntries; i++) begin
      entry_data[i] = (i + 1) * 8'h11;  // e.g. 0x11, 0x22, 0x33, 0x44
    end

    // Reset sequence
    repeat (4) @(posedge clk);
    @(negedge clk);
    rst = 1'b0;
    repeat (2) @(posedge clk);

    // 1) Allocate all 4 entries
    $display("Starting allocation of %0d entries", NumEntries);
    for (int i = 0; i < NumEntries; i++) begin
      // Wait until DUT asserts alloc_valid (DUT->TB)
      wait (alloc_valid == 1'b1);

      // Drive alloc_ready at negedge
      @(negedge clk);
      alloc_ready = 1'b1;
      allocated_ids[i] = alloc_entry_id;
      if (alloc_entry_id !== i) begin
        $display("ERROR: expected alloc_entry_id %0d, got %0d", i, alloc_entry_id);
        $fatal;
      end
      $display("  Alloc cycle %0d: got entry_id %0d", i, alloc_entry_id);

      // De-assert alloc_ready at negedge
      @(negedge clk);
      alloc_ready = 1'b0;

      // Wait a posedge before next iteration
      @(posedge clk);
    end

    // Wait a few cycles to confirm alloc_valid goes low
    @(posedge clk);
    if (alloc_valid) begin
      $display("ERROR: alloc_valid did not go low after allocating all entries");
      $fatal;
    end
    $display("All entries allocated, alloc_valid is now low as expected.");

    // 2) Deallocate them in a different order

    $display("Starting deallocation in a different order");
    for (int j = 0; j < NumEntries; j++) begin
      // We pick the reorder index from 'allocated_ids'
      automatic int idx = reorder[j];

      // Drive dealloc signals at negedge
      @(negedge clk);
      unordered_resp_push_valid    = 1'b1;
      unordered_resp_push_entry_id = allocated_ids[idx];
      unordered_resp_push_data     = entry_data[allocated_ids[idx]];

      $display("  Dealloc cycle %0d: sending entry_id %0d, data 0x%0h", j, allocated_ids[idx],
               unordered_resp_push_data);

      // De-assert at next negedge
      @(negedge clk);
      unordered_resp_push_valid    = 1'b0;
      unordered_resp_push_entry_id = '0;
      unordered_resp_push_data     = '0;

      // Wait a few cycles
      repeat (1) @(posedge clk);
    end

    // 3) Read them off the reordered_resp_pop interface in original order
    //    They should come off as allocated_ids[0], allocated_ids[1], etc.
    //    with the correct data from entry_data[].
    $display("Reading from reordered_resp_pop interface and checking order/data");
    for (int k = 0; k < NumEntries; k++) begin
      // Wait for a valid cycle (DUT->TB)
      wait (reordered_resp_pop_valid == 1'b1);

      @(negedge clk);

      // Check data at this point
      if (reordered_resp_pop_data !== entry_data[allocated_ids[k]]) begin
        $display("ERROR: data mismatch for entry %0d. Expected: 0x%0h, Got: 0x%0h",
                 allocated_ids[k], entry_data[allocated_ids[k]], reordered_resp_pop_data);
        $fatal;
      end
      $display("  Received correct data=0x%0h at cycle %0t", reordered_resp_pop_data, $time);

      // Consume it
      @(negedge clk);
      reordered_resp_pop_ready = 1'b1;
      @(negedge clk);
      reordered_resp_pop_ready = 1'b0;

      // Wait a few cycles
      repeat (1) @(posedge clk);
    end

    repeat (100) @(posedge clk);

    $display("TEST PASSED");
    $finish;
  end

endmodule
