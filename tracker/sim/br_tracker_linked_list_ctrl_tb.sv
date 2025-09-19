// SPDX-License-Identifier: Apache-2.0

module br_tracker_linked_list_ctrl_tb;
  parameter int NumLinkedLists = 1;
  parameter int Depth = 5;
  parameter int NumWritePorts = 1;
  parameter int RamReadLatency = 0;
  localparam int AddressWidth = $clog2(Depth);
  localparam int CountWidth = $clog2(Depth + 1);

  logic clk;
  logic rst;

  logic [NumWritePorts-1:0] next_tail_valid;
  logic [NumWritePorts-1:0][AddressWidth-1:0] next_tail;

  logic head_valid;
  logic head_ready;
  logic [AddressWidth-1:0] head;

  logic empty;
  logic [CountWidth-1:0] items;

  logic [NumWritePorts-1:0] ptr_ram_wr_valid;
  logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_addr;
  logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_data;
  logic ptr_ram_rd_addr_valid;
  logic [AddressWidth-1:0] ptr_ram_rd_addr;
  logic ptr_ram_rd_data_valid;
  logic [AddressWidth-1:0] ptr_ram_rd_data;


  br_tracker_linked_list_ctrl #(
      .NumLinkedLists(NumLinkedLists),
      .Depth(Depth),
      .NumWritePorts(NumWritePorts),
      .RamReadLatency(RamReadLatency)
  ) dut (
      .clk,
      .rst,
      .next_tail_valid,
      .next_tail,
      .head_valid,
      .head_ready,
      .head,
      .empty,
      .items,
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data
  );

  br_ram_flops #(
      .Depth(Depth),
      .Width(AddressWidth),
      .AddressDepthStages(RamReadLatency),
      .NumWritePorts(NumWritePorts)
  ) br_ram_flops (
      .wr_clk(clk),
      .wr_rst(rst),
      .wr_valid(ptr_ram_wr_valid),
      .wr_addr(ptr_ram_wr_addr),
      .wr_data(ptr_ram_wr_data),
      .wr_word_en({NumWritePorts{1'b1}}),
      .rd_clk(clk),
      .rd_rst(rst),
      .rd_addr_valid(ptr_ram_rd_addr_valid),
      .rd_addr(ptr_ram_rd_addr),
      .rd_data_valid(ptr_ram_rd_data_valid),
      .rd_data(ptr_ram_rd_data)
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    next_tail_valid = '0;
    next_tail = '0;
    head_ready = '0;

    td.reset_dut();

    td.check(empty, "List not empty after reset.");
    td.check_integer(items, 0, "List has items after reset.");
    td.check(!head_valid, "List has head valid after reset.");

    td.wait_cycles(1);

    // Fill up the list with a single port
    for (int i = 0; i < Depth; i++) begin
      next_tail_valid[0] = 1;
      next_tail[0] = i;

      td.wait_cycles(1);
    end

    next_tail_valid[0] = 0;

    td.check_integer(items, Depth, "List has the wrong number of items.");
    td.check(!empty, "List is unexpectedly empty after pushing.");

    // Pop all the entries
    head_ready = 1;

    for (int i = 0; i < Depth; i++) begin
      while (!head_valid) td.wait_cycles(1);

      td.check_integer(head, i, "Head is the wrong address.");
      td.wait_cycles(1);
    end

    head_ready = 0;

    td.check(empty, "List is unexpectedly non-empty after popping.");
    td.check_integer(items, 0, "List has items after popping.");
    td.check(!head_valid, "List has head valid after popping.");

    if (NumWritePorts > 1) begin
      next_tail_valid = '1;
      // Push an entry from each port over two cycles
      for (int i = 0; i < 2; i++) begin
        for (int j = 0; j < NumWritePorts; j++) begin
          next_tail[j] = i * NumWritePorts + j;
        end

        td.wait_cycles();
      end

      next_tail_valid = '0;

      td.check_integer(items, 2 * NumWritePorts, "List has the wrong number of items.");

      head_ready = 1;

      // Pop all the entries and check the order
      for (int i = 0; i < 2 * NumWritePorts; i++) begin
        while (!head_valid) td.wait_cycles(1);
        td.check_integer(head, i, "Head is the wrong address.");
        td.wait_cycles();
      end

      head_ready = 0;

      td.check(empty, "List is unexpectedly non-empty after popping.");
      td.check_integer(items, 0, "List has items after popping.");
      td.check(!head_valid, "List has head valid after popping.");
    end

    td.finish();
  end

endmodule
