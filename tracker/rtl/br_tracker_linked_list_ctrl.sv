// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_tracker_linked_list_ctrl #(
    // Depth of the RAM. Must be at least 2.
    parameter int Depth = 2,
    // Number of write ports. Must be at least 1 and at most Depth.
    parameter int NumWritePorts = 1,
    // Number of linked lists. Must be at least 1 and less than Depth.
    parameter int NumLinkedLists = 1,
    // Number of cycles to read from the pointer RAM. Must be at least 0.
    parameter int RamReadLatency = 0,

    localparam int AddressWidth = $clog2(Depth),
    localparam int CountWidth   = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [NumWritePorts-1:0] next_tail_valid,
    input logic [NumWritePorts-1:0][AddressWidth-1:0] next_tail,

    output logic head_valid,
    input logic head_ready,
    output logic [AddressWidth-1:0] head,

    output logic empty,
    output logic [CountWidth-1:0] items,

    output logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_addr,
    output logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_data,

    output logic ptr_ram_rd_addr_valid,
    output logic [AddressWidth-1:0] ptr_ram_rd_addr,
    input logic ptr_ram_rd_data_valid,
    input logic [AddressWidth-1:0] ptr_ram_rd_data
);

  // Integration assertions
  `BR_ASSERT_STATIC(legal_depth_a, Depth >= 2)
  `BR_ASSERT_STATIC(legal_num_write_ports_a, NumWritePorts >= 1 && NumWritePorts <= Depth)
  `BR_ASSERT_STATIC(legal_num_linked_lists_a, NumLinkedLists >= 1 && NumLinkedLists < Depth)
  `BR_ASSERT_STATIC(legal_ram_read_latency_a, RamReadLatency >= 0)

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_next_tail_checks
    `BR_ASSERT_INTG(next_tail_in_range_a, next_tail_valid[i] |-> next_tail[i] < Depth)
  end

  if (RamReadLatency == 0) begin : gen_zero_read_latency_check
    `BR_ASSERT_INTG(ptr_ram_rd_zero_latency_a, ptr_ram_rd_addr_valid == ptr_ram_rd_data_valid)
  end else begin : gen_nonzero_read_latency_check
    `BR_ASSERT_INTG(
        expected_read_latency_a,
        ##(RamReadLatency) ptr_ram_rd_data_valid == $past(ptr_ram_rd_addr_valid, RamReadLatency))
  end

  // Implementation

  localparam int ChangeWidth = $clog2(NumWritePorts + 1);

  // LL head/tail selection
  // If there are multiple linked lists, we need to cycle through
  // the head/tail pointers in round-robin fashion.

  logic [NumLinkedLists-1:0] ll_empty, ll_empty_next;
  logic [NumLinkedLists-1:0] ll_head_bypass;
  logic [NumLinkedLists-1:0][CountWidth-1:0] ll_count, ll_count_next;
  logic [NumLinkedLists-1:0] ll_head_valid;
  logic [NumLinkedLists-1:0] ll_head_last;
  logic [NumLinkedLists-1:0][AddressWidth-1:0] ll_head;
  logic [NumLinkedLists-1:0][AddressWidth-1:0] ll_tail;
  // Encode head/tail selector as onehot for timing reasons.
  logic [NumLinkedLists-1:0] ll_head_select_read;
  logic [NumLinkedLists-1:0] ll_head_select_write;
  logic [NumLinkedLists-1:0] ll_tail_select;
  logic [NumWritePorts-1:0][NumLinkedLists-1:0] ll_next_tail_valid;
  logic [NumLinkedLists-1:0][NumWritePorts-1:0] ll_next_tail_valid_transpose;
  logic [NumWritePorts-1:0][NumLinkedLists-1:0] ll_ptr_ram_wr_valid;
  logic [NumWritePorts-1:0][NumLinkedLists-1:0][AddressWidth-1:0] ll_ptr_ram_wr_addr;

  if (NumLinkedLists > 1) begin : gen_ll_head_tail_select_shift_reg
    logic ll_head_select_update;

    // ll_head_select_read rotates by 1 for each head pop
    br_delay_shift_reg #(
        .NumStages(NumLinkedLists),
        .EnableCoverReinit(0)
    ) br_delay_shift_reg_head (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value(NumLinkedLists'(1'b1)),
        .value(ll_head_select_read),
        .shift_en(ll_head_select_update),
        .shift_in(ll_head_select_read[NumLinkedLists-1]),
        .shift_out()
    );

    assign ll_head_select_update = head_valid && head_ready;

    // ll_tail_select rotates by 1 for each write port that is valid
    // There can be up to NumWritePorts rotation per cycle.
    localparam int RotateWidth = $clog2(NumWritePorts + 1);

    logic ll_tail_select_update;
    logic [RotateWidth-1:0] ll_tail_select_rotate;
    logic [NumLinkedLists-1:0] ll_tail_select_next;

    br_enc_countones #(
        .Width(NumWritePorts)
    ) br_enc_countones_ll_tail_select_rotate (
        .in(next_tail_valid),
        .count(ll_tail_select_rotate)
    );

    br_shift_rotate #(
        .NumSymbols (NumLinkedLists),
        .SymbolWidth(1),
        .MaxRotate  (NumWritePorts)
    ) br_shift_rotate_ll_tail_select (
        .in(ll_tail_select),
        .right(1'b0),
        .rotate(ll_tail_select_rotate),
        .out(ll_tail_select_next)
    );

    assign ll_tail_select_update = |next_tail_valid;

    `BR_REGLI(ll_tail_select, ll_tail_select_next, ll_tail_select_update, NumLinkedLists'(1'b1))

    // Only used for assertion
    logic ll_head_select_write_valid;  // ri lint_check_waive NOT_READ

    br_delay_valid #(
        .NumStages(RamReadLatency),
        .Width(NumLinkedLists)
    ) br_delay_valid_ll_head_select (
        .clk,
        .rst,
        .in_valid(ptr_ram_rd_addr_valid),
        .in(ll_head_select_read),
        .out_valid(ll_head_select_write_valid),
        .out(ll_head_select_write),
        .out_valid_stages(),
        .out_stages()
    );

    `BR_ASSERT_IMPL(ptr_ram_rd_latency_match_a, ptr_ram_rd_data_valid == ll_head_select_write_valid)
  end else begin : gen_single_ll_head_tail_select
    assign ll_tail_select = 1'b1;
    assign ll_head_select_read = 1'b1;
    assign ll_head_select_write = 1'b1;
  end

  // Because we cycle through linked lists, the maximum number of writes
  // on a given cycle to a single linked list is the ceiling division
  // of the number of write ports by the number of linked lists.
  localparam int MaxWritesPerLLPerCycle = br_math::ceil_div(NumWritePorts, NumLinkedLists);

  if (NumWritePorts > 1) begin : gen_multi_wport_ll_next_tail_valid
    if (NumLinkedLists > 1) begin : gen_multi_ll_next_tail_valid
      // To get ll_next_tail_valid for each write port, we take the ll_tail_select
      // and rotate left by the number of preceding write ports that are valid.
      logic [NumWritePorts-1:0][NumLinkedLists-1:0] ll_tail_select_rotated;

      // The first rotated tail select is not rotated as there aren't any preceding
      // write ports.
      assign ll_tail_select_rotated[0] = ll_tail_select;

      for (genvar i = 1; i < NumWritePorts; i++) begin : gen_ll_tail_select_rotated
        localparam int MaxRotate = i;
        localparam int RotateWidth = $clog2(MaxRotate + 1);

        logic [RotateWidth-1:0] rotate;

        br_enc_countones #(
            .Width(i)
        ) br_enc_countones_ll_next_tail_valid (
            .in(next_tail_valid[i-1:0]),
            .count(rotate)
        );

        br_shift_rotate #(
            .NumSymbols (NumLinkedLists),
            .SymbolWidth(1),
            .MaxRotate  (MaxRotate)
        ) br_shift_rotate_ll_tail_select (
            .in(ll_tail_select),
            .right(1'b0),
            .rotate,
            .out(ll_tail_select_rotated[i])
        );
      end

      for (genvar i = 0; i < NumWritePorts; i++) begin : gen_ll_next_tail_valid
        assign ll_next_tail_valid[i] =
            {NumLinkedLists{next_tail_valid[i]}} & ll_tail_select_rotated[i];
      end
    end else begin : gen_single_ll_next_tail_valid
      assign ll_next_tail_valid = next_tail_valid & {NumWritePorts{ll_tail_select}};
    end
  end else begin : gen_single_wport_ll_next_tail_valid
    assign ll_next_tail_valid = {NumLinkedLists{next_tail_valid}} & ll_tail_select;
  end

  for (genvar i = 0; i < NumLinkedLists; i++) begin : gen_linked_list
    for (genvar j = 0; j < NumWritePorts; j++) begin : gen_ll_next_tail_valid_transpose
      assign ll_next_tail_valid_transpose[i][j] = ll_next_tail_valid[j][i];
    end

    logic counter_decr_valid;
    logic [ChangeWidth-1:0] counter_decr;
    logic counter_incr_valid;
    logic [ChangeWidth-1:0] counter_incr;

    assign counter_incr_valid = |ll_next_tail_valid_transpose[i];
    br_enc_countones #(
        .Width(NumWritePorts)
    ) br_enc_countones_ll_next_tail_valid (
        .in(ll_next_tail_valid_transpose[i]),
        .count(counter_incr)
    );

    assign counter_decr_valid = head_valid && head_ready && ll_head_select_read[i];
    assign counter_decr = ChangeWidth'(1'b1);

    br_counter #(
        .MaxValue(Depth),
        .MaxChange(NumWritePorts),
        // Because writes have to cycle through linked lists,
        // you can't actually have NumWritePorts all pushing to the same
        // list on a given cycle.
        .MaxIncrement(br_math::ceil_div(NumWritePorts, NumLinkedLists)),
        .MaxDecrement(1),
        .EnableWrap(0),
        .EnableCoverReinit(0),
        .EnableCoverZeroChange(0)
    ) br_counter_ll_count (
        .clk,
        .rst,
        .reinit(1'b0),
        .initial_value(CountWidth'(1'b0)),
        .decr_valid(counter_decr_valid),
        .decr(counter_decr),
        .incr_valid(counter_incr_valid),
        .incr(counter_incr),
        .value(ll_count[i]),
        .value_next(ll_count_next[i])
    );

    assign ll_empty_next[i] = ll_count_next[i] == '0;
    `BR_REGI(ll_empty[i], ll_empty_next[i], 1'b1)

    logic ll_head_update;
    logic ll_head_update_from_next_tail;
    logic ll_head_update_from_ptr_ram;
    logic [AddressWidth-1:0] ll_head_next;
    logic ll_tail_update;
    logic [AddressWidth-1:0] ll_tail_next;
    logic ll_head_valid_next;
    logic ll_head_clear;

    assign ll_tail_update = |ll_next_tail_valid_transpose[i];
    // This is the last head if there's only one element left.
    assign ll_head_last[i] = (ll_count[i] == 'd1);
    // Bypass the tail to the head in one of the following cases:
    // 1. The list is empty.
    // 2. There is a single item left in the list and it is currently being popped.
    assign ll_head_bypass[i] =
        ll_empty[i] ||
        (ll_head_last[i] && ll_head_valid[i] && ll_head_select_read[i] && head_ready);

    if (NumWritePorts <= NumLinkedLists) begin : gen_tail_update_no_chaining
      // If the number of write ports is less than or equal to the number of linked lists,
      // we can never have multiple write ports hitting the same linked list on a given cycle.
      // The next tail can just come from a onehot mux (or pass through if only a single write port).
      if (NumWritePorts == 1) begin : gen_single_wport_next_tail
        assign ll_tail_next = next_tail[0];
      end else begin : gen_multi_wport_next_tail
        br_mux_onehot #(
            .SymbolWidth (AddressWidth),
            .NumSymbolsIn(NumWritePorts)
        ) br_mux_onehot_ll_next_tail (
            .select(ll_next_tail_valid_transpose[i]),
            .in(next_tail),
            .out(ll_tail_next)
        );
      end

      for (genvar j = 0; j < NumWritePorts; j++) begin : gen_ll_ptr_ram_write
        // Only write next_tail to the pointer RAM if the linked list is not empty.
        // If it's empty, there's no valid address to write to!
        // The next_tail will become both the tail and the head for the previously
        // empty list.
        assign ll_ptr_ram_wr_valid[j][i] = ll_next_tail_valid[j][i] && !ll_empty[i];
        assign ll_ptr_ram_wr_addr[j][i]  = ll_tail[i];
      end

      assign ll_head_next = ll_head_bypass[i] ? ll_tail_next : ptr_ram_rd_data;
    end else begin : gen_tail_update_chaining
      // If multiple write ports are hitting the same linked list,
      // we need to chain the updates. The pointer RAM write address
      // will be the current tail for the first write and the next tail
      // of the previous write for subsequent writes.
      // ll_tail_next will be the next tail from the last active write port.
      // On empty, ll_head_next will be the next tail from the first active write port.
      logic [AddressWidth-1:0] ll_head_next_from_tail;

      // First write port never writes when list is empty.
      assign ll_ptr_ram_wr_valid[0][i] = ll_next_tail_valid[0][i] && !ll_empty[i];
      assign ll_ptr_ram_wr_addr[0][i] = ll_tail[i];

      // Second write port does not write on next_tail update if
      // list is empty and there was no update from the first write port.
      assign ll_ptr_ram_wr_valid[1][i] = ll_next_tail_valid[1][i] &&
          (!ll_empty[i] || ll_next_tail_valid[0][i]);
      assign ll_ptr_ram_wr_addr[1][i] = ll_next_tail_valid[0][i] ? next_tail[0] : ll_tail[i];

      if (NumWritePorts > 2) begin : gen_subsequent_ptr_ram_write
        for (genvar j = 2; j < NumWritePorts; j++) begin : gen_ll_ptr_ram_write
          // Need to pick the previous tail to use for the address
          // based on the last previous port to get a tail update.
          // The write ports ahead of the current one are rotating through
          // the linked lists, so the maximum number that could be pushing
          // to the same linked list as this is the ceiling division of the
          // number of write ports before this by the number of linked lists.
          localparam int MaxInHot = br_math::ceil_div(j, NumLinkedLists);
          logic [j-1:0] prev_tail_select;
          logic [AddressWidth-1:0] prev_tail;

          br_enc_priority_encoder #(
              .NumRequesters(j),
              .MsbHighestPriority(1),
              .MaxInHot(MaxInHot)
          ) br_enc_priority_encoder_prev_tail_select (
              .clk,
              .rst,
              .in (ll_next_tail_valid_transpose[i][j-1:0]),
              .out(prev_tail_select)
          );

          br_mux_onehot #(
              .SymbolWidth (AddressWidth),
              .NumSymbolsIn(j)
          ) br_mux_onehot_prev_tail_select (
              .select(prev_tail_select),
              .in(next_tail[j-1:0]),
              .out(prev_tail)
          );
          // No write if list is empty and no previous write ports updated.
          assign ll_ptr_ram_wr_valid[j][i] = ll_next_tail_valid[j][i] &&
              (!ll_empty[i] || (|ll_next_tail_valid_transpose[i][j-1:0]));
          // If no previous port is updating this linked list, use the current tail
          // as the address. Otherwise, use the next tail from the previous port.
          assign ll_ptr_ram_wr_addr[j][i] =
              (|ll_next_tail_valid_transpose[i][j-1:0]) ?  prev_tail : ll_tail[i];
        end
      end

      // Find the next tail. This will be the next_tail from the last active write port.
      logic [NumWritePorts-1:0] ll_tail_next_select;
      logic [NumWritePorts-1:0] ll_head_next_select;

      br_enc_priority_encoder #(
          .NumRequesters(NumWritePorts),
          .MsbHighestPriority(1),
          .MaxInHot(MaxWritesPerLLPerCycle)
      ) br_enc_priority_encoder_ll_tail_next_select (
          .clk,
          .rst,
          .in (ll_next_tail_valid_transpose[i]),
          .out(ll_tail_next_select)
      );

      br_mux_onehot #(
          .SymbolWidth (AddressWidth),
          .NumSymbolsIn(NumWritePorts)
      ) br_mux_onehot_ll_next_tail (
          .select(ll_tail_next_select),
          .in(next_tail),
          .out(ll_tail_next)
      );

      br_enc_priority_encoder #(
          .NumRequesters(NumWritePorts),
          .MsbHighestPriority(0),
          .MaxInHot(MaxWritesPerLLPerCycle)
      ) br_enc_priority_encoder_ll_head_next_select (
          .clk,
          .rst,
          .in (ll_next_tail_valid_transpose[i]),
          .out(ll_head_next_select)
      );

      br_mux_onehot #(
          .SymbolWidth (AddressWidth),
          .NumSymbolsIn(NumWritePorts)
      ) br_mux_onehot_ll_head_next (
          .select(ll_head_next_select),
          .in(next_tail),
          .out(ll_head_next_from_tail)
      );

      assign ll_head_next = ll_head_bypass[i] ? ll_head_next_from_tail : ptr_ram_rd_data;
    end

    assign ll_head_update_from_next_tail = ll_tail_update && ll_head_bypass[i];
    assign ll_head_update_from_ptr_ram = ptr_ram_rd_data_valid && ll_head_select_write[i];
    assign ll_head_update = ll_head_update_from_next_tail || ll_head_update_from_ptr_ram;

    `BR_ASSERT(no_head_update_conflict_a,
               !(ll_head_update_from_next_tail && ll_head_update_from_ptr_ram))

    `BR_REGL(ll_tail[i], ll_tail_next, ll_tail_update)
    `BR_REGL(ll_head[i], ll_head_next, ll_head_update)

    // Clear ll_head_valid if the head is read. Set it if head is updated.
    assign ll_head_clear = head_valid && head_ready && ll_head_select_read[i];
    assign ll_head_valid_next = (ll_head_valid[i] && !ll_head_clear) || ll_head_update;

    `BR_REG(ll_head_valid[i], ll_head_valid_next)
  end

  logic ptr_ram_rd_needed;

  assign head_valid = |(ll_head_select_read & ~ll_empty & ll_head_valid);

  // Need to read next head from pointer RAM when the head is popped
  // Only exception is if this is the last head in a list.
  assign ptr_ram_rd_needed = |(ll_head_select_read & ~ll_head_last);
  assign ptr_ram_rd_addr_valid = head_valid && head_ready && ptr_ram_rd_needed;
  assign ptr_ram_rd_addr = head;

  if (NumLinkedLists > 1) begin : gen_multi_ll_head_read
    br_mux_onehot #(
        .SymbolWidth (AddressWidth),
        .NumSymbolsIn(NumLinkedLists)
    ) br_mux_onehot_ptr_ram_rd_addr (
        .select(ll_head_select_read),
        .in(ll_head),
        .out(head)
    );
  end else begin : gen_single_ll_head_read
    assign head = ll_head[0];
  end

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_ptr_ram_write
    assign ptr_ram_wr_valid[i] = |ll_ptr_ram_wr_valid[i];

    if (NumLinkedLists > 1) begin : gen_multi_ll_ptr_ram_write
      br_mux_onehot #(
          .SymbolWidth (AddressWidth),
          .NumSymbolsIn(NumLinkedLists)
      ) br_mux_onehot_ptr_ram_wr_addr (
          .select(ll_ptr_ram_wr_valid[i]),
          .in(ll_ptr_ram_wr_addr[i]),
          .out(ptr_ram_wr_addr[i])
      );

      // Make sure that only one linked list writes to a given port in a cycle.
      `BR_ASSERT_IMPL(ll_ptr_ram_wr_valid_onehot_a, $onehot0(ll_ptr_ram_wr_valid[i]))
    end else begin : gen_single_ll_ptr_ram_write
      assign ptr_ram_wr_addr[i] = ll_ptr_ram_wr_addr[i][0];
    end
    assign ptr_ram_wr_data[i] = next_tail[i];
  end

  assign empty = &ll_empty;

  always_comb begin : gen_items
    items = 0;
    for (int i = 0; i < NumLinkedLists; i++) begin
      items += ll_count[i];
    end
  end

  // Implementation assertions

  `BR_ASSERT_IMPL(items_zero_on_empty_a, empty == (items == 0))
  `BR_ASSERT_IMPL(no_head_valid_when_empty_a, empty |-> !head_valid)

  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(AddressWidth)
  ) br_flow_checks_valid_data_impl_head (
      .clk,
      .rst,
      .valid(head_valid),
      .ready(head_ready),
      .data (head)
  );

endmodule
