// Copyright 2025 The Bedrock-RTL Authors
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

module br_ram_initializer_monitor #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic [Width-1:0] initial_value,
    input logic start,
    input logic busy,
    input logic wr_valid,
    input logic [AddressWidth-1:0] wr_addr,
    input logic [Width-1:0] wr_data
);

  Initialization_Start #(
      .Depth(Depth),
      .Width(Width)
  ) Initialization_Start_inst (
      .*
  );
  Initialization_Completion #(
      .Depth(Depth),
      .Width(Width)
  ) Initialization_Completion_inst (
      .*
  );
  Sequential_Addressing #(
      .Depth(Depth),
      .Width(Width)
  ) Sequential_Addressing_inst (
      .*
  );
  Initialization_No_Start_When_Busy #(
      .Depth(Depth),
      .Width(Width)
  ) Initialization_No_Start_When_Busy_inst (
      .*
  );
  Initial_Value_Stability #(
      .Depth(Depth),
      .Width(Width)
  ) Initial_Value_Stability_inst (
      .*
  );
  Unified_Reset_Scenario #(
      .Depth(Depth),
      .Width(Width)
  ) Unified_Reset_Scenario_inst (
      .*
  );
  Write_Valid_Signal_Assertion #(
      .Depth(Depth),
      .Width(Width)
  ) Write_Valid_Signal_Assertion_inst (
      .*
  );
  Sequential_Address_Increment #(
      .Depth(Depth),
      .Width(Width)
  ) Sequential_Address_Increment_inst (
      .*
  );
  Data_Integrity_During_Initialization #(
      .Depth(Depth),
      .Width(Width)
  ) Data_Integrity_During_Initialization_inst (
      .*
  );
  Completion_of_Initialization #(
      .Depth(Depth),
      .Width(Width)
  ) Completion_of_Initialization_inst (
      .*
  );
  Advanced_Verification_Check #(
      .Depth(Depth),
      .Width(Width)
  ) Advanced_Verification_Check_inst (
      .*
  );
endmodule



module Initialization_Start #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic start,
    input logic busy,
    input logic wr_valid
);

  // Initialization Start: Cover that: `start` is asserted, after one clock cycle `busy` is asserted, after one clock cycle `wr_valid` is asserted.
  init_start_C :
  cover property (@(posedge clk) start ##1 busy ##1 wr_valid);
endmodule



module Initialization_Completion #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic busy,
    input logic wr_valid
);

  // Initialization Completion: Cover that: `busy` is asserted, eventually `busy` is deasserted, eventually `wr_valid` is deasserted.
  init_completion_C :
  cover property (@(posedge clk) busy ##[1:$] !busy ##[1:$] !wr_valid);
endmodule



module Sequential_Addressing #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic wr_valid,
    input logic [AddressWidth-1:0] wr_addr
);

  // Sequential Addressing: Cover that: `wr_valid` is asserted, `wr_addr` starts at 0 and increments sequentially until it reaches `Depth-1`.
  sequential_addressing_C :
  cover property (@(posedge clk) wr_valid && (wr_addr == 0) ##[1:$] (wr_addr == Depth - 1));
endmodule


module Initialization_No_Start_When_Busy #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic start,
    input logic busy
);

  // Assume that 'start' cannot be asserted when 'busy' is asserted
  no_start_when_busy_A :
  assume property (@(posedge clk) disable iff (rst) busy |-> !start);
endmodule



module Initial_Value_Stability #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic [Width-1:0] initial_value,
    input logic busy
);

  // Assume that 'initial_value' must remain stable while 'busy' is asserted to ensure data consistency during write operations.
  initial_value_stability_A :
  assume property (@(posedge clk) disable iff (rst) busy |-> $stable(initial_value));
endmodule



module Unified_Reset_Scenario #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic busy,
    input logic wr_valid,
    input logic [AddressWidth-1:0] wr_addr,
    input logic [Width-1:0] wr_data
);

  // Unified Reset Scenario: Verify that when 'rst' is asserted ('1') and then deasserted ('0'), the output signals 'busy', 'wr_valid', and 'wr_addr' are all reset to '0' on the same clock cycle.
  unified_reset_A :
  assert property (@(posedge clk) $fell(
      rst
  ) |-> (busy == 0 && wr_valid == 0 && wr_addr == 0));
endmodule



module Write_Valid_Signal_Assertion #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic busy,
    input logic wr_valid
);

  // Assert that `wr_valid` is asserted only when `busy` is asserted.
  wr_valid_when_busy_A :
  assert property (@(posedge clk) disable iff (rst) (wr_valid |-> busy));
endmodule



module Sequential_Address_Increment #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic start,
    input logic busy,
    input logic wr_valid,
    input logic [AddressWidth-1:0] wr_addr
);

  // Sequential Address Increment: Check that `wr_addr` starts at 0 and increments sequentially by 1 on each clock cycle while `busy` is asserted.
  initial_addr_A :
  assert property (@(posedge clk) disable iff (rst) $rose(busy) |-> wr_valid && (wr_addr == 0));
  sequential_addr_incr_A :
  assert property (@(posedge clk) disable iff (rst) busy && $stable(busy) |->
    wr_valid && (wr_addr == $past(wr_addr) + 1));
endmodule



module Data_Integrity_During_Initialization #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic [Width-1:0] initial_value,
    input logic wr_valid,
    input logic [Width-1:0] wr_data
);

  // Data Integrity During Initialization: Check that `wr_data` always matches `initial_value` during the initialization process.
  data_integrity_A :
  assert property (@(posedge clk) disable iff (rst) wr_valid |-> (wr_data == initial_value));
endmodule



module Completion_of_Initialization #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic start,
    input logic busy,
    input logic [AddressWidth-1:0] wr_addr
);

  // Completion of Initialization: Check that once `start` is asserted, `busy` is eventually deasserted after all addresses from 0 to `Depth-1` have been initialized.
  initialization_complete_A :
  assert property (@(posedge clk) disable iff (rst) start |-> s_eventually (!busy));
  initialize_last_addr_A :
  assert property (@(posedge clk) disable iff (rst) start |-> s_eventually (wr_addr == Depth-1));
endmodule



module Advanced_Verification_Check #(
    parameter int Depth = 2,
    parameter int Width = 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic [Width-1:0] initial_value,
    input logic start,
    input logic busy,
    input logic wr_valid,
    input logic [AddressWidth-1:0] wr_addr,
    input logic [Width-1:0] wr_data
);

  logic [Depth-1:0] addr_written;

  always_ff @(posedge clk) begin
    if (rst) begin
      addr_written <= '0;
    end else if (wr_valid) begin
      addr_written[wr_addr] <= 1'b1;
    end
  end

  // Ensure `initial_value` is written to each address from 0 to `Depth-1`.
  for (genvar addr = 0; addr < Depth; addr++) begin
    write_initial_value_A :
    assert property (@(posedge clk) disable iff (rst) wr_valid && wr_addr == addr |->
        wr_data == initial_value);
  end

  all_addr_eventually_written_A :
  assert property (@(posedge clk) disable iff (rst) start |-> ##[1:$] (addr_written == '1));

  // Ensure `busy` is deasserted only after the final address is written.
  busy_deassert_after_final_write_A :
  assert property (@(posedge clk) disable iff (rst) busy && wr_valid && wr_addr == (Depth - 1) |=>
    !busy);

  exactly_n_cycles_A :
  assert property (@(posedge clk) disable iff (rst) $rose(busy) |-> ##Depth $fell(busy));
endmodule

bind br_ram_initializer br_ram_initializer_monitor #(
    .Depth(Depth),
    .Width(Width)
) monitor (
    .clk(clk),
    .rst(rst),
    .initial_value(initial_value),
    .start(start),
    .busy(busy),
    .wr_valid(wr_valid),
    .wr_addr(wr_addr),
    .wr_data(wr_data)
);
