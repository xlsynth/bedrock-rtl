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

// Basic checker of br_flow_reg

`include "br_asserts.svh"

module br_flow_reg_basic_fpv_monitor #(
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability
) (
    input logic             clk,
    input logic             rst,
    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data
);

  // ----------FV assumptions----------
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))

  if (EnableAssertPushValidStability) begin : gen_push_valid
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  end
  if (EnableAssertPushDataStability) begin : gen_push_data
    `BR_ASSUME(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data))
  end

  // ----------Sanity Check----------
  if (EnableAssertPushValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid && !pop_ready |=> pop_valid)
  end
  if (EnableAssertPushDataStability) begin : gen_pop_data
    `BR_ASSERT(pop_data_stable_a, pop_valid && !pop_ready |=> $stable(pop_data))
  end

  // ----------Data integrity Check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(2)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid & push_ready),
      .incoming_data(push_data),
      .outgoing_vld(pop_valid & pop_ready),
      .outgoing_data(pop_data)
  );

endmodule : br_flow_reg_basic_fpv_monitor
