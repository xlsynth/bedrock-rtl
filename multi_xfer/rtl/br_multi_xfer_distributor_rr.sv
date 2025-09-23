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

// Bedrock-RTL Multi-Transfer Interface Distributor (Round-Robin)
//
// This module takes a multi-transfer sendable/receivable interface of
// NumSymbols size and fans out the data to NumSymbols ready/valid
// flows. If data is sendable from the push interface, the distributor
// will send the data to the pop flows that are ready to accept.
// If there are more ready flows than sendable data, the flows to
// which data will be sent will be selected by multi-grant
// round-robin arbitration. If there are fewer ready flows than
// sendable data, only the lower data symbols will be sent.
// The remaining undistributed symbols must be shifted down by the sender
// according to the multi-transfer interface specification.

module br_multi_xfer_distributor_rr #(
    // The number of symbols that can be transferred in a single cycle.
    // Must be at least 2.
    parameter int NumSymbols = 2,
    // The width of each symbol. Must be at least 1.
    parameter int SymbolWidth = 1,
    // The number of flows to distribute to. Must be at least NumSymbols.
    parameter int NumFlows = 2,
    // If 1, cover that push_sendable can be greater than push_receivable.
    // If 0, assert that push_sendable is always less than or equal to push_receivable.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_data is stable when push_sendable > push_receivable.
    // If 0, cover that push_data is unstable when push_sendable > push_receivable.
    parameter bit EnableAssertPushDataStability = 1,
    // If 1, assert that push_sendable is 0 at the end of simulation.
    parameter bit EnableAssertFinalNotSendable = 1,

    localparam int CountWidth = $clog2(NumSymbols + 1)
) (
    input logic clk,
    input logic rst,

    input logic [CountWidth-1:0] push_sendable,
    output logic [CountWidth-1:0] push_receivable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] push_data,

    output logic [NumFlows-1:0] pop_valid,
    input logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0][SymbolWidth-1:0] pop_data
);

  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] grant;
  logic [NumSymbols-1:0][NumFlows-1:0] grant_ordered;
  logic [CountWidth-1:0] grant_count;
  logic [CountWidth-1:0] grant_allowed;
  logic enable_priority_update;

  br_multi_xfer_distributor_core #(
      .NumSymbols(NumSymbols),
      .SymbolWidth(SymbolWidth),
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotSendable(EnableAssertFinalNotSendable)
  ) br_multi_xfer_distributor_core_inst (
      .clk,
      .rst,
      .push_sendable,
      .push_receivable,
      .push_data,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .request,
      .grant_allowed,
      .grant,
      .grant_ordered,
      .grant_count,
      .enable_priority_update
  );

  br_arb_multi_rr #(
      .NumRequesters(NumFlows),
      .MaxGrantPerCycle(NumSymbols),
      .EnableCoverBlockPriorityUpdate(0)
  ) br_arb_multi_rr_inst (
      .clk,
      .rst,
      .request,
      .grant,
      .grant_allowed,
      .grant_ordered,
      .grant_count,
      .enable_priority_update
  );
endmodule
