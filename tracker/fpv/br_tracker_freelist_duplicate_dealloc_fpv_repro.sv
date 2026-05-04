// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for duplicate deallocation credit counting in br_tracker_freelist.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_freelist_duplicate_dealloc_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int NumEntries = 4;
  localparam int NumAllocPerCycle = 1;
  localparam int NumDeallocPorts = 2;
  localparam int EntryIdWidth = $clog2(NumEntries);
  localparam int AllocCountWidth = $clog2(NumAllocPerCycle + 1);
  localparam int DeallocCountWidth = $clog2(NumDeallocPorts + 1);

  logic [2:0] cycle;
  logic [AllocCountWidth-1:0] alloc_receivable;
  logic [AllocCountWidth-1:0] alloc_sendable;
  logic [NumAllocPerCycle-1:0][EntryIdWidth-1:0] alloc_entry_id;
  logic [NumDeallocPorts-1:0] dealloc_valid;
  logic [NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id;
  logic [DeallocCountWidth-1:0] dealloc_count;

  br_tracker_freelist #(
      .NumEntries(NumEntries),
      .NumAllocPerCycle(NumAllocPerCycle),
      .NumDeallocPorts(NumDeallocPorts),
      .RegisterAllocOutputs(0),
      .EnableBypass(1)
  ) dut (
      .clk,
      .rst,
      .alloc_receivable,
      .alloc_sendable,
      .alloc_entry_id,
      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_count
  );

  assign alloc_receivable = !rst && cycle == 3'd0 ? 1'b1 : '0;
  assign dealloc_valid = !rst && cycle == 3'd2 ? 2'b11 : '0;
  assign dealloc_entry_id[0] = '0;
  assign dealloc_entry_id[1] = '0;

  `BR_REG(cycle, cycle + 3'd1)

  `BR_ASSERT(duplicate_dealloc_count_a,
             cycle == 3'd2 && dealloc_valid == 2'b11 &&
                 dealloc_entry_id[0] == dealloc_entry_id[1] |-> dealloc_count == 1)

endmodule : br_tracker_freelist_duplicate_dealloc_fpv_repro
