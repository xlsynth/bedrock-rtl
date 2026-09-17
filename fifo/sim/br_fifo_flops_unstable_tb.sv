// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

// Fills the FIFO, changes and revokes a blocked push, then verifies that only accepted data drains
// in order. The test covers the unstable push contract independently of the wrapped FIFO logic.
module br_fifo_flops_unstable_tb #(
    parameter int Depth = 13,
    parameter int Width = 8,
    parameter int RegisterPopOutputs = 0,
    parameter int FlopRamAddressDepthStages = 0
);
  localparam int TimeoutCycles = Depth + FlopRamAddressDepthStages + RegisterPopOutputs + 10;

  logic clk;
  logic rst;

  logic push_ready;
  logic push_valid_unstable;
  logic [Width-1:0] push_data_unstable;

  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  logic empty;
  logic full;
  logic [$clog2(Depth+1)-1:0] items;
  logic [$clog2(Depth+1)-1:0] slots;

  br_fifo_flops_unstable #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid_unstable,
      .push_data_unstable,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty,
      .empty_next(),
      .slots,
      .slots_next(),
      .full,
      .full_next (),
      .items,
      .items_next()
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    int timeout;

    push_valid_unstable = 1'b0;
    push_data_unstable = '0;
    pop_ready = 1'b0;

    td.reset_dut();
    #1;
    td.check(push_ready, "empty FIFO should accept a push");
    td.check(empty, "FIFO should be empty after reset");

    // Fill the FIFO with known accepted data while the pop side is blocked.
    for (int item = 0; item < Depth; item++) begin
      @(negedge clk);
      push_valid_unstable = 1'b1;
      push_data_unstable  = Width'(item + 1);
      #1;
      td.check(push_ready, "FIFO should accept each fill item");
      @(posedge clk);
    end

    @(negedge clk);
    #1;
    td.check(!push_ready, "full FIFO should backpressure the push side");
    td.check(full, "FIFO should report full after the fill");

    timeout = TimeoutCycles;
    while (!pop_valid && (timeout > 0)) begin
      @(negedge clk);
      timeout = timeout - 1;
    end
    td.check(timeout > 0, "first accepted item did not reach the pop interface");
    td.check(pop_data === Width'(1), "first accepted item should remain at the pop interface");

    // Change data while valid remains asserted and push_ready remains low.
    push_data_unstable = '1;
    #1;
    td.check(!push_ready, "changed blocked push should remain unaccepted");
    td.check(pop_data === Width'(1), "blocked data change must not disturb the pop item");
    @(posedge clk);

    @(negedge clk);
    push_data_unstable = '0;
    #1;
    td.check(!push_ready, "second changed blocked push should remain unaccepted");
    td.check(pop_data === Width'(1), "second blocked data change must not disturb the pop item");
    @(posedge clk);

    // Revoke the blocked push. None of the blocked values may enter the FIFO.
    @(negedge clk);
    push_valid_unstable = 1'b0;
    push_data_unstable  = '1;
    #1;
    td.check(!push_ready, "revoked blocked push should remain unaccepted");
    td.check(pop_data === Width'(1), "blocked valid revocation must not disturb the pop item");

    pop_ready = 1'b1;
    for (int item = 0; item < Depth; item++) begin
      timeout = TimeoutCycles;
      while (!pop_valid && (timeout > 0)) begin
        @(negedge clk);
        timeout = timeout - 1;
      end
      td.check(timeout > 0, "accepted item did not reach the pop interface");
      td.check(pop_data === Width'(item + 1), "accepted FIFO data drained out of order");
      @(posedge clk);
      if (item != (Depth - 1)) begin
        @(negedge clk);
      end
    end

    @(negedge clk);
    pop_ready = 1'b0;
    #1;
    td.check(empty, "FIFO should be empty after draining accepted data");
    td.check(!pop_valid, "blocked push values must not appear at the pop interface");
    td.check(items == '0, "FIFO item count should return to zero");
    td.check(slots == Depth, "FIFO slot count should return to its capacity");

    td.finish();
  end

endmodule : br_fifo_flops_unstable_tb
