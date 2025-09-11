// SPDX-License-Identifier: Apache-2.0

module br_tracker_freelist_tb;

  parameter int NumEntries = 16;
  parameter int NumAllocPerCycle = 1;
  parameter int NumDeallocPorts = 1;
  parameter int NumAllocations = 100;
  parameter int MaxDelay = 10;

  localparam int EntryIdWidth = $clog2(NumEntries);
  localparam int AllocCountWidth = $clog2(NumAllocPerCycle + 1);

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

  logic [AllocCountWidth-1:0] alloc_sendable;
  logic [AllocCountWidth-1:0] alloc_receivable;
  logic [NumAllocPerCycle-1:0][EntryIdWidth-1:0] alloc_entry_id;

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
      .NumAllocPerCycle(NumAllocPerCycle),
      .NumDeallocPorts(NumDeallocPorts)
  ) dut (
      .clk,
      .rst,

      .alloc_sendable,
      .alloc_receivable,
      .alloc_entry_id,

      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_count()
  );

  // Allocate all entries at the beginning without deallocation
  // and check that they come out in the expected order.
  task automatic init_allocate_entries();
    alloc_receivable = NumAllocPerCycle;

    // The entries are going to be allocated to the ports in round-robin
    // fashion initially.
    for (int i = 0; i < NumEntries; i += NumAllocPerCycle) begin
      @(posedge clk);
      td.check_integer(alloc_sendable, NumAllocPerCycle, "Invalid number of allocatable entries");

      for (int j = 0; j < NumAllocPerCycle; j++) begin
        td.check_integer(alloc_entry_id[j], i + j, "Allocated entry ID is incorrect");
        free_entries[i+j] = 1;
        entry_queues[0].push_back(i + j);
      end
    end
    @(negedge clk);
    alloc_receivable = 0;
  endtask

  // Randomly allocate entries to queues
  task automatic random_allocate_entries();
    int delay;
    int qid;
    int alloced;
    int to_alloc;
    int cycle_alloced;

    $display("Randomly allocating entries");

    alloced = 0;

    while (alloced < NumAllocations) begin
      int timeout;

      delay = $urandom_range(MaxDelay);
      td.wait_cycles(delay);

      to_alloc = $urandom_range(1, NumAllocPerCycle);
      to_alloc = br_math::min2(to_alloc, NumAllocations - alloced);

      alloc_receivable = to_alloc;
      @(posedge clk);

      timeout = (MaxDelay + 1);
      while (alloc_sendable == '0 && timeout > 0) begin
        @(posedge clk);
        timeout--;
      end

      td.check(timeout != '0, $sformatf("Timeout waiting for allocation"));

      cycle_alloced = br_math::min2(to_alloc, alloc_sendable);

      for (int i = 0; i < cycle_alloced; i++) begin
        if (cycle_alloced > i) begin
          td.check(free_entries[alloc_entry_id[i]], $sformatf(
                   "Allocated entry %0d is not free", alloc_entry_id[i]));
          qid = $urandom_range(NumDeallocPorts - 1);
          entry_queues[qid].push_back(alloc_entry_id[i]);
          free_entries[alloc_entry_id[i]] = 1;
        end
      end

      @(negedge clk);

      alloc_receivable = '0;
      alloced += cycle_alloced;
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
    alloc_receivable = 0;
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

    random_allocate_entries();

    td.wait_cycles(1);

    $display("Waiting for deallocations to complete");
    wait_for_quiesce();
    check_all_free();

    td.finish();
  end
endmodule
