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

// Bedrock-RTL Flow Demux with Select

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_flow_demux_select_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertSelectStability = 0,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                                   clk,
    input logic                                   rst,
    input logic [$clog2(NumFlows)-1:0]            select,
    input logic                                   push_ready,
    input logic                                   push_valid,
    input logic [           Width-1:0]            push_data,
    input logic [        NumFlows-1:0]            pop_ready,
    input logic [        NumFlows-1:0]            pop_valid,
    input logic [        NumFlows-1:0][Width-1:0] pop_data
);

  // ----------Instantiate basic checks----------
  br_flow_demux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertSelectStability(EnableAssertSelectStability),
      // Output flow reg ensures that pop is always stable
      .EnableAssertPopValidStability(1),
      .EnableAssertPopDataStability(1)
  ) fv_checker (
      .clk,
      .rst,
      .select,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  // ----------FV assumptions----------
  `BR_ASSUME(select_range_a, select < NumFlows)

  // ----------select check----------
  logic [Width-1:0] fv_data;
  `BR_REGLN(fv_data, push_data, push_valid & push_ready)

  // select aligns with push interface
  `BR_ASSERT(select_data_check_a, push_valid & push_ready |=> pop_data[$past(select)] == fv_data)
  `BR_ASSERT(forward_progress_a, push_valid |=> pop_valid[$past(select)])

endmodule : br_flow_demux_select_fpv_monitor

bind br_flow_demux_select br_flow_demux_select_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertSelectStability(EnableAssertSelectStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
