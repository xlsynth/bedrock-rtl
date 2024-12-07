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

// AXI4-Lite 1:2 Split
//
// This module splits an AXI4-Lite interface into two separate AXI4-Lite
// interfaces. The intended use case is to create a "narrow" branch that
// is controlled by configuration parameters. If a transaction address
// falls within the range of the branch, it is routed to the branch. If
// the transaction address does not fall within the range of the branch, it
// is routed to the "trunk" interface.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_amba_axil_split #(
    parameter int AddrWidth = 40,  // Must be at least 12
    parameter int DataWidth = 64,  // Must be at least 32
    parameter int AWUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int ARUserWidth = 1,
    parameter int RUserWidth = 1,
    parameter logic [AddrWidth-1:0] BranchStartAddr = {AddrWidth{1'b0}},
    parameter logic [AddrWidth-1:0] BranchEndAddr = {AddrWidth{1'b1}},
    parameter int MaxOutstandingReads = 1,  // Must be at least 1
    parameter int MaxOutstandingWrites = 1,  // Must be at least 1
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite root target interface
    input  logic [            AddrWidth-1:0] root_awaddr,
    input  logic [br_amba::AxiProtWidth-1:0] root_awprot,
    input  logic [          AWUserWidth-1:0] root_awuser,
    input  logic                             root_awvalid,
    output logic                             root_awready,
    input  logic [            DataWidth-1:0] root_wdata,
    input  logic [          StrobeWidth-1:0] root_wstrb,
    input  logic [           WUserWidth-1:0] root_wuser,
    input  logic                             root_wvalid,
    output logic                             root_wready,
    output logic [br_amba::AxiRespWidth-1:0] root_bresp,
    output logic                             root_bvalid,
    input  logic                             root_bready,
    input  logic [            AddrWidth-1:0] root_araddr,
    input  logic [br_amba::AxiProtWidth-1:0] root_arprot,
    input  logic [          ARUserWidth-1:0] root_aruser,
    input  logic                             root_arvalid,
    output logic                             root_arready,
    output logic [            DataWidth-1:0] root_rdata,
    output logic [br_amba::AxiRespWidth-1:0] root_rresp,
    output logic [           RUserWidth-1:0] root_ruser,
    output logic                             root_rvalid,
    input  logic                             root_rready,

    // AXI4-Lite trunk initiator interface
    output logic [            AddrWidth-1:0] trunk_awaddr,
    output logic [br_amba::AxiProtWidth-1:0] trunk_awprot,
    output logic [          AWUserWidth-1:0] trunk_awuser,
    output logic                             trunk_awvalid,
    input  logic                             trunk_awready,
    output logic [            DataWidth-1:0] trunk_wdata,
    output logic [          StrobeWidth-1:0] trunk_wstrb,
    output logic [           WUserWidth-1:0] trunk_wuser,
    output logic                             trunk_wvalid,
    input  logic                             trunk_wready,
    input  logic [br_amba::AxiRespWidth-1:0] trunk_bresp,
    input  logic                             trunk_bvalid,
    output logic                             trunk_bready,
    output logic [            AddrWidth-1:0] trunk_araddr,
    output logic [br_amba::AxiProtWidth-1:0] trunk_arprot,
    output logic [          ARUserWidth-1:0] trunk_aruser,
    output logic                             trunk_arvalid,
    input  logic                             trunk_arready,
    input  logic [            DataWidth-1:0] trunk_rdata,
    input  logic [br_amba::AxiRespWidth-1:0] trunk_rresp,
    input  logic [           RUserWidth-1:0] trunk_ruser,
    input  logic                             trunk_rvalid,
    output logic                             trunk_rready,

    // AXI4-Lite branch initiator interface
    output logic [            AddrWidth-1:0] branch_awaddr,
    output logic [br_amba::AxiProtWidth-1:0] branch_awprot,
    output logic [          AWUserWidth-1:0] branch_awuser,
    output logic                             branch_awvalid,
    input  logic                             branch_awready,
    output logic [            DataWidth-1:0] branch_wdata,
    output logic [          StrobeWidth-1:0] branch_wstrb,
    output logic [           WUserWidth-1:0] branch_wuser,
    output logic                             branch_wvalid,
    input  logic                             branch_wready,
    input  logic [br_amba::AxiRespWidth-1:0] branch_bresp,
    input  logic                             branch_bvalid,
    output logic                             branch_bready,
    output logic [            AddrWidth-1:0] branch_araddr,
    output logic [br_amba::AxiProtWidth-1:0] branch_arprot,
    output logic [          ARUserWidth-1:0] branch_aruser,
    output logic                             branch_arvalid,
    input  logic                             branch_arready,
    input  logic [            DataWidth-1:0] branch_rdata,
    input  logic [br_amba::AxiRespWidth-1:0] branch_rresp,
    input  logic [           RUserWidth-1:0] branch_ruser,
    input  logic                             branch_rvalid,
    output logic                             branch_rready
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_at_least_32_a, DataWidth >= 32)
  `BR_ASSERT_STATIC(branch_end_addr_after_start_addr_a, BranchEndAddr > BranchStartAddr)
  `BR_ASSERT_STATIC(max_out_reads_must_be_at_least_1_a, MaxOutstandingReads >= 1)
  `BR_ASSERT_STATIC(max_out_writes_must_be_at_least_1_a, MaxOutstandingWrites >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  localparam int ReadCounterWidth = $clog2(MaxOutstandingReads + 1);
  localparam int WriteCounterWidth = $clog2(MaxOutstandingWrites + 1);

  logic branch_awaddr_in_range, branch_araddr_in_range;
  logic branch_bvalid_req, trunk_bvalid_req;
  logic branch_rvalid_req, trunk_rvalid_req;
  logic branch_bvalid_grant, trunk_bvalid_grant;
  logic branch_rvalid_grant, trunk_rvalid_grant;
  logic [ ReadCounterWidth-1:0] outstanding_reads_count;
  logic [WriteCounterWidth-1:0] outstanding_writes_count;
  logic no_outstanding_reads, no_outstanding_writes;
  logic last_arvalid_is_branch, last_awvalid_is_branch;
  logic ar_handshake_valid, aw_handshake_valid;
  logic r_handshake_valid, b_handshake_valid;

  // AXI handshake signals
  assign ar_handshake_valid = root_arvalid && root_arready;
  assign r_handshake_valid = root_rvalid && root_rready;
  assign aw_handshake_valid = root_awvalid && root_awready;
  assign b_handshake_valid = root_bvalid && root_bready;

  // ri lint_check_off INVALID_COMPARE
  assign branch_awaddr_in_range = (root_awaddr >= BranchStartAddr) &&
                                  (root_awaddr <= BranchEndAddr);
  assign branch_araddr_in_range = (root_araddr >= BranchStartAddr) &&
                                  (root_araddr <= BranchEndAddr);
  // ri lint_check_on INVALID_COMPARE

  // Counters to track outstanding read transactions
  br_counter #(
      .MaxValue  (MaxOutstandingReads),
      .MaxChange (1),
      .EnableWrap(0)
  ) br_counter_outstanding_reads (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value({ReadCounterWidth{1'b0}}),
      .incr_valid(ar_handshake_valid),
      .incr(1'b1),
      .decr_valid(r_handshake_valid),
      .decr(1'b1),
      .value(outstanding_reads_count),
      .value_next()  // ri lint_check_waive OPEN_OUTPUT
  );

  assign no_outstanding_reads = (outstanding_reads_count == 0);

  // Track the last read tranasctions, if it was trunk or branch
  `BR_REGLN(last_arvalid_is_branch, branch_araddr_in_range, ar_handshake_valid)

  // Split the read address channel
  assign trunk_arvalid = root_arvalid && !branch_araddr_in_range &&
                         (no_outstanding_reads || !last_arvalid_is_branch);
  assign branch_arvalid = root_arvalid && branch_araddr_in_range &&
                          (no_outstanding_reads || last_arvalid_is_branch);
  assign root_arready = (trunk_arvalid && trunk_arready) || (branch_arvalid && branch_arready);

  // Counters to track outstanding write transactions
  br_counter #(
      .MaxValue  (MaxOutstandingWrites),
      .MaxChange (1),
      .EnableWrap(0)
  ) br_counter_outstanding_writes (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value({WriteCounterWidth{1'b0}}),
      .incr_valid(aw_handshake_valid),
      .incr(1'b1),
      .decr_valid(b_handshake_valid),
      .decr(1'b1),
      .value(outstanding_writes_count),
      .value_next()  // ri lint_check_waive OPEN_OUTPUT
  );


  assign no_outstanding_writes = (outstanding_writes_count == 0);

  // Track the last tranasctions, if it was trunk or branch
  `BR_REGLN(last_awvalid_is_branch, branch_awaddr_in_range, aw_handshake_valid)

  // Split the write address and write data channels
  // - Need to hold write address and write data until both are valid
  assign trunk_awvalid = root_awvalid && root_wvalid && !branch_awaddr_in_range &&
                          (no_outstanding_writes || !last_awvalid_is_branch);
  assign branch_awvalid = root_awvalid && root_wvalid && branch_awaddr_in_range &&
                          (no_outstanding_writes || last_awvalid_is_branch);
  assign trunk_wvalid = root_awvalid && root_wvalid && !branch_awaddr_in_range &&
                         (no_outstanding_writes || !last_awvalid_is_branch);
  assign branch_wvalid = root_awvalid && root_wvalid && branch_awaddr_in_range &&
                         (no_outstanding_writes || last_awvalid_is_branch);
  assign root_awready = (trunk_awvalid && trunk_awready) || (branch_awvalid && branch_awready);
  assign root_wready = (trunk_wvalid && trunk_wready) || (branch_wvalid && branch_wready);

  // Broadcast the write address, read address, and write data signals to the branch and trunk.
  assign {trunk_awaddr, branch_awaddr} = {2{root_awaddr}};
  assign {trunk_awprot, branch_awprot} = {2{root_awprot}};
  assign {trunk_awuser, branch_awuser} = {2{root_awuser}};
  assign {trunk_wdata, branch_wdata} = {2{root_wdata}};
  assign {trunk_wstrb, branch_wstrb} = {2{root_wstrb}};
  assign {trunk_wuser, branch_wuser} = {2{root_wuser}};
  assign {trunk_araddr, branch_araddr} = {2{root_araddr}};
  assign {trunk_arprot, branch_arprot} = {2{root_arprot}};
  assign {trunk_aruser, branch_aruser} = {2{root_aruser}};

  // Read Response Channel Arbitration
  br_arb_rr #(
      .NumRequesters(2)
  ) br_arb_rr_rvalid (
      .clk(clk),
      .rst(rst),
      .enable_priority_update(1'b0),
      .request({branch_rvalid_req, trunk_rvalid_req}),
      .grant({branch_rvalid_grant, trunk_rvalid_grant})
  );

  // Assign the read response signal based on the arbiter grant
  assign branch_rvalid_req = branch_rvalid && root_rready;
  assign trunk_rvalid_req = trunk_rvalid && root_rready;
  assign root_rvalid = branch_rvalid || trunk_rvalid;
  assign root_rresp = trunk_rvalid_grant ? trunk_rresp : branch_rresp;
  assign root_rdata = trunk_rvalid_grant ? trunk_rdata : branch_rdata;
  assign root_ruser = trunk_rvalid_grant ? trunk_ruser : branch_ruser;
  assign branch_rready = branch_rvalid_grant;
  assign trunk_rready = trunk_rvalid_grant;

  // Write Response Channel Arbitration
  br_arb_rr #(
      .NumRequesters(2)
  ) br_arb_rr_bvalid (
      .clk(clk),
      .rst(rst),
      .enable_priority_update(1'b0),
      .request({branch_bvalid_req, trunk_bvalid_req}),
      .grant({branch_bvalid_grant, trunk_bvalid_grant})
  );

  // Assign the write response signals based on the arbiter grant
  assign branch_bvalid_req = branch_bvalid && root_bready;
  assign trunk_bvalid_req = trunk_bvalid && root_bready;
  assign root_bvalid = branch_bvalid || trunk_bvalid;
  assign root_bresp = trunk_bvalid_grant ? trunk_bresp : branch_bresp;
  assign branch_bready = branch_bvalid_grant;
  assign trunk_bready = trunk_bvalid_grant;

endmodule : br_amba_axil_split
