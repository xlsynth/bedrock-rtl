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
// Push Controller for CDC FIFO with Ready/Valid interface

`include "br_asserts_internal.svh"

module br_cdc_fifo_push_ctrl #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int RamWriteLatency = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,

    // Signals to/from pop controller
    input  logic [CountWidth-1:0] pop_count_gray,
    output logic [CountWidth-1:0] push_count_gray,
    input  logic                  reset_active_pop,
    output logic                  reset_active_push
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_COVER_INTG(full_c, full)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic push_beat;

  br_cdc_fifo_push_flag_mgr #(
      .Depth(Depth),
      .RamWriteLatency(RamWriteLatency)
  ) br_cdc_fifo_push_flag_mgr (
      .clk,
      .rst,
      .push_beat,
      .push_count_gray,
      .pop_count_gray,
      .pop_count_delta(),
      .slots_next,
      .slots,
      .full_next,
      .full,
      .reset_active_push,
      .reset_active_pop
  );

  // Core flow-control logic
  br_fifo_push_ctrl_core #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(1'b0)  // Bypass is not enabled for CDC
  ) br_fifo_push_ctrl_core (
      .clk,
      .rst,

      .push_ready,
      .push_valid,
      .push_data,

      .bypass_ready(1'b0),  // Bypass not used
      .bypass_valid_unstable(),  // Bypass not used
      .bypass_data_unstable(),  // Bypass not used

      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,

      .full,
      .push_beat
  );

  // Implementation checks
  // Implementation checks
  `BR_ASSERT_IMPL(ram_wr_addr_in_range_a, ram_wr_valid |-> ram_wr_addr < Depth)

  // Flow control and latency
  `BR_ASSERT_IMPL(push_backpressure_when_full_a, full |-> !push_ready)

  // Flags
  `BR_ASSERT_IMPL(slots_in_range_a, slots <= Depth)
  `BR_ASSERT_IMPL(slots_next_a, ##1 slots == $past(slots_next))
  // Slots should only decrease on a push
  `BR_ASSERT_IMPL(push_slots_a, (slots_next < slots) |-> push_beat)
  `BR_ASSERT_IMPL(full_a, full == (slots == 0))

endmodule : br_cdc_fifo_push_ctrl
