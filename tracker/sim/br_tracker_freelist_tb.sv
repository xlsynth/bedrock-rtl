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

module br_tracker_freelist_tb;

  parameter int NumEntries = 16;
  parameter int NumAllocPorts = 1;
  parameter int NumDeallocPorts = 1;
  parameter int NumAllocations = 100 / NumAllocPorts;
  parameter int MaxDelay = 10;

  localparam int EntryIdWidth = $clog2(NumEntries);

  // In the testbench, we create a queue for each deallocation port.  The
  // allocation thread will allocate entries and push them to a randomly
  // selected queue. The deallocation threads will pop the corresponding queue
  // and deallocate the entry. A free_entries bit-vector is maintained which is
  // marked 0 on allocation and 1 on deallocation. We do not check a particular
  // order of entry allocation after the initial allocation of all entries. Just
  // check that we don't allocate an entry that is not supposed to be free.

  logic [EntryIdWidth-1:0] entry_queues[NumDeallocPorts][$];
  logic [NumEntries-1:0] free_entries;

  logic clk;
  logic rst;

  logic [NumAllocPorts-1:0] alloc_valid;
  logic [NumAllocPorts-1:0] alloc_ready;
  logic [NumAllocPorts-1:0][EntryIdWidth-1:0] alloc_entry_id;

  logic [NumDeallocPorts-1:0] dealloc_valid;
  logic [NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id;

  br_test_driver #(
      .ResetCycles(4)
  ) td (
      .clk,
      .rst
  );

  br_tracker_freelist #(
      .NumEntries(NumEntries),
      .NumAllocPorts(NumAllocPorts),
      .NumDeallocPorts(NumDeallocPorts)
  ) dut (
      .clk,
      .rst,

      .alloc_valid,
      .alloc_ready,
      .alloc_entry_id,

      .dealloc_valid,
      .dealloc_entry_id
  );

  // Allocate all entries at the beginning without deallocation
  // and check that they come out in the expected order.
  task automatic init_allocate_entries();
    alloc_ready = '1;

    // The entries are going to be allocated to the ports in round-robin
    // fashion initially.
    for (int i = 0; i < NumEntries; i += NumAllocPorts) begin
      @(posedge clk);
      for (int j = 0; j < NumAllocPorts; j++) begin
        td.check(alloc_valid[j], "Cannot allocate an initial entry");
        td.check_integer(alloc_entry_id[j], i + j, "Allocated entry ID is incorrect");
        free_entries[i+j] = 1;
        entry_queues[0].push_back(i + j);
      end
    end
    @(negedge clk);
    alloc_ready = '0;
  endtask

  // Randomly allocate entries to queues
  task automatic random_allocate_entries(int aid);
    int delay;
    int qid;

    $display("Randomly allocating entries for alloc port %0d", aid);

    for (int i = 0; i < NumAllocations; i++) begin
      int timeout;

      delay = $urandom_range(MaxDelay);
      td.wait_cycles(delay);

      alloc_ready[aid] = 1;
      @(posedge clk);

      timeout = (MaxDelay + 1) * NumAllocPorts * NumAllocations;
      while (!alloc_valid[aid] && timeout > 0) begin
        @(posedge clk);
        timeout--;
      end

      td.check(alloc_valid[aid], $sformatf("Timeout waiting for allocation on %0d", aid));

      td.check(free_entries[alloc_entry_id[aid]], $sformatf(
               "Allocated entry %0d is not free", alloc_entry_id[aid]));

      qid = $urandom_range(NumDeallocPorts - 1);
      entry_queues[qid].push_back(alloc_entry_id[aid]);
      free_entries[alloc_entry_id[aid]] = 0;

      @(negedge clk);
      alloc_ready[aid] = 0;
    end
  endtask

  // Wait for all of the allocated entries to be deallocated
  task automatic wait_for_quiesce();
    int quiesced;
    int timeout;

    quiesced = 0;
    timeout  = 1000;

    while (!quiesced && timeout > 0) begin
      quiesced = 1;
      foreach (entry_queues[i]) begin
        if (entry_queues[i].size() > 0) begin
          quiesced = 0;
          break;
        end
      end
      td.wait_cycles(1);
      timeout--;
    end

    td.check(quiesced, "Timeout waiting for deallocations to complete");
  endtask

  // Check that all entries have returned to the queue at the end of the test
  task automatic check_all_free();
    foreach (free_entries[i]) begin
      td.check(free_entries[i], $sformatf("Entry %0d is not free at end of test", i));
    end
  endtask

  // Deallocate entries from a particular queue
  task automatic deallocate_entries(int qid);
    int delay;
    $display("Checking for entries to deallocate on queue %0d", qid);
    forever begin
      if (entry_queues[qid].size() > 0) begin
        delay = $urandom_range(MaxDelay);
        td.wait_cycles(delay);

        dealloc_valid[qid] = 1;
        dealloc_entry_id[qid] = entry_queues[qid].pop_front();
        free_entries[dealloc_entry_id[qid]] = 1;
        td.wait_cycles(1);
        dealloc_valid[qid] = 0;
      end
      td.wait_cycles(1);
    end
  endtask

  initial begin
    alloc_ready = 0;
    dealloc_valid = 0;
    dealloc_entry_id = 0;
    free_entries = '1;

    td.reset_dut();
    td.wait_cycles(4);

    $display("Allocate all initial entries");
    init_allocate_entries();

    foreach (entry_queues[i]) begin
      automatic int qid;
      qid = i;
      fork
        deallocate_entries(qid);
      join_none
    end

    fork
      begin
        // Need to wait for all the allocation threads to finish,
        // but don't want to wait for the deallocation threads.
        for (int i = 0; i < NumAllocPorts; i++) begin
          automatic int aid;
          aid = i;
          fork
            random_allocate_entries(aid);
          join_none
        end
        wait fork;
      end
    join

    td.wait_cycles(1);

    $display("Waiting for deallocations to complete");
    wait_for_quiesce();
    check_all_free();

    td.finish();
  end
endmodule
