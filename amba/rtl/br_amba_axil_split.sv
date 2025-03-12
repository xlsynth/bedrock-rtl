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

// Bedrock-RTL AXI4-Lite 1:2 Split
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
    parameter int MaxOutstandingReads = 1,  // Must be at least 1
    parameter int MaxOutstandingWrites = 1,  // Must be at least 1
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset
    input logic [AddrWidth-1:0] branch_start_addr,
    input logic [AddrWidth-1:0] branch_end_addr,

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
  `BR_ASSERT_INTG(branch_end_addr_after_start_addr_a, branch_end_addr > branch_start_addr)
  `BR_ASSERT_STATIC(max_out_reads_must_be_at_least_1_a, MaxOutstandingReads >= 1)
  `BR_ASSERT_STATIC(max_out_writes_must_be_at_least_1_a, MaxOutstandingWrites >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  localparam int ReadCounterWidth = $clog2(MaxOutstandingReads + 1);
  localparam int WriteCounterWidth = $clog2(MaxOutstandingWrites + 1);

  logic branch_awaddr_in_range, branch_araddr_in_range;
  logic [ ReadCounterWidth-1:0] outstanding_reads_count;
  logic [WriteCounterWidth-1:0] outstanding_writes_count;
  logic no_outstanding_reads, no_outstanding_writes;
  logic last_arvalid_is_branch, last_awvalid_is_branch;
  logic ar_handshake_valid, aw_handshake_valid;
  logic r_handshake_valid, b_handshake_valid;

  logic [AddrWidth-1:0] root_awaddr_reg;
  logic [br_amba::AxiProtWidth-1:0] root_awprot_reg;
  logic [AWUserWidth-1:0] root_awuser_reg;
  logic [DataWidth-1:0] root_wdata_reg;
  logic [StrobeWidth-1:0] root_wstrb_reg;
  logic [WUserWidth-1:0] root_wuser_reg;
  logic write_addr_flow_reg_is_branch;
  logic write_data_flow_reg_is_branch;
  logic write_addr_flow_reg_push_valid, write_addr_flow_reg_push_ready;
  logic write_addr_flow_reg_pop_valid, write_addr_flow_reg_pop_ready;
  logic write_data_flow_reg_push_valid, write_data_flow_reg_push_ready;
  logic write_data_flow_reg_pop_valid, write_data_flow_reg_pop_ready;

  // AXI handshake signals
  assign ar_handshake_valid = root_arvalid && root_arready;
  assign r_handshake_valid = root_rvalid && root_rready;
  assign aw_handshake_valid = root_awvalid && root_awready;
  assign b_handshake_valid = root_bvalid && root_bready;

  // ri lint_check_off INVALID_COMPARE
  assign branch_awaddr_in_range = (root_awaddr >= branch_start_addr) &&
                                  (root_awaddr <= branch_end_addr);
  assign branch_araddr_in_range = (root_araddr >= branch_start_addr) &&
                                  (root_araddr <= branch_end_addr);
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

  // Track the last read transaction, if it was trunk or branch
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

  // Since the write data can arrive before the write address, we need to hold write address and
  // write data until both are valid so we know which branch to route the data to. However, since
  // awready and wready are not guaranteed to be driven by registers, add a flow register to
  // prevent combinational loops.
  br_flow_reg_both #(
      .Width(AddrWidth + br_amba::AxiProtWidth + AWUserWidth + 1)
  ) br_flow_reg_both_write_addr (
      .clk,
      .rst,

      .push_ready(write_addr_flow_reg_push_ready),
      .push_valid(write_addr_flow_reg_push_valid),
      .push_data ({root_awaddr, root_awprot, root_awuser, branch_awaddr_in_range}),

      .pop_ready(write_addr_flow_reg_pop_ready),
      .pop_valid(write_addr_flow_reg_pop_valid),
      .pop_data ({root_awaddr_reg, root_awprot_reg, root_awuser_reg, write_addr_flow_reg_is_branch})
  );

  br_flow_reg_both #(
      .Width(DataWidth + StrobeWidth + WUserWidth + 1)
  ) br_flow_reg_both_write_data (
      .clk,
      .rst,

      .push_ready(write_data_flow_reg_push_ready),
      .push_valid(write_data_flow_reg_push_valid),
      .push_data ({root_wdata, root_wstrb, root_wuser, branch_awaddr_in_range}),

      .pop_ready(write_data_flow_reg_pop_ready),
      .pop_valid(write_data_flow_reg_pop_valid),
      .pop_data ({root_wdata_reg, root_wstrb_reg, root_wuser_reg, write_data_flow_reg_is_branch})
  );

  // Push to the flow register when both the write address and write data are valid and the flow
  // register is ready to accept the data
  assign write_addr_flow_reg_push_valid = root_awvalid && root_wvalid &&
      write_addr_flow_reg_push_ready && write_data_flow_reg_push_ready &&
      (no_outstanding_writes || (last_awvalid_is_branch == branch_awaddr_in_range));
  assign write_data_flow_reg_push_valid = root_awvalid && root_wvalid &&
      write_addr_flow_reg_push_ready && write_data_flow_reg_push_ready &&
      (no_outstanding_writes || (last_awvalid_is_branch == branch_awaddr_in_range));

  // Track the last write transaction, if it was trunk or branch
  `BR_REGLN(last_awvalid_is_branch, branch_awaddr_in_range, aw_handshake_valid)

  // Do not drive the ready signal until the write address and write data are valid and the flow
  // register is ready to accept the data
  assign root_awready = write_addr_flow_reg_push_valid;
  assign root_wready = write_data_flow_reg_push_valid;

  // Split the write address and write data channels based on the awaddr
  assign trunk_awvalid = write_addr_flow_reg_pop_valid && !write_addr_flow_reg_is_branch;
  assign branch_awvalid = write_addr_flow_reg_pop_valid && write_addr_flow_reg_is_branch;
  assign trunk_wvalid = write_data_flow_reg_pop_valid && !write_data_flow_reg_is_branch;
  assign branch_wvalid = write_data_flow_reg_pop_valid && write_data_flow_reg_is_branch;

  // Pop from the flow register when the branch or trunk accepts the write address and write data
  assign write_addr_flow_reg_pop_ready =
      (trunk_awvalid && trunk_awready) || (branch_awvalid && branch_awready);
  assign write_data_flow_reg_pop_ready =
      (trunk_wvalid && trunk_wready) || (branch_wvalid && branch_wready);

  // Broadcast the write address, read address, and write data signals to the branch and trunk.
  assign {trunk_awaddr, branch_awaddr} = {2{root_awaddr_reg}};
  assign {trunk_awprot, branch_awprot} = {2{root_awprot_reg}};
  assign {trunk_awuser, branch_awuser} = {2{root_awuser_reg}};
  assign {trunk_wdata, branch_wdata} = {2{root_wdata_reg}};
  assign {trunk_wstrb, branch_wstrb} = {2{root_wstrb_reg}};
  assign {trunk_wuser, branch_wuser} = {2{root_wuser_reg}};
  assign {trunk_araddr, branch_araddr} = {2{root_araddr}};
  assign {trunk_arprot, branch_arprot} = {2{root_arprot}};
  assign {trunk_aruser, branch_aruser} = {2{root_aruser}};

  // Read Response Channel Merge
  assign root_rvalid = branch_rvalid || trunk_rvalid;
  assign root_rresp = ({br_amba::AxiRespWidth{trunk_rvalid}} & trunk_rresp) |
                      ({br_amba::AxiRespWidth{branch_rvalid}} & branch_rresp);
  assign root_rdata = ({DataWidth{trunk_rvalid}} & trunk_rdata) |
                      ({DataWidth{branch_rvalid}} & branch_rdata);
  assign root_ruser = ({RUserWidth{trunk_rvalid}} & trunk_ruser) |
                      ({RUserWidth{branch_rvalid}} & branch_ruser);
  assign {trunk_rready, branch_rready} = {2{root_rready}};

  // Write Response Channel Merge
  assign root_bvalid = branch_bvalid || trunk_bvalid;
  assign root_bresp = ({br_amba::AxiRespWidth{trunk_bvalid}} & trunk_bresp) |
                      ({br_amba::AxiRespWidth{branch_bvalid}} & branch_bresp);
  assign {trunk_bready, branch_bready} = {2{root_bready}};

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  `BR_ASSERT_IMPL(last_arvalid_is_branch_is_valid_a, !$isunknown(last_arvalid_is_branch)
                  || no_outstanding_reads)
  `BR_ASSERT_IMPL(last_awvalid_is_branch_is_valid_a, !$isunknown(last_awvalid_is_branch)
                  || no_outstanding_writes)
  `BR_ASSERT_IMPL(rvalid_is_onehot_a, !(branch_rvalid && trunk_rvalid))
  `BR_ASSERT_IMPL(bvalid_is_onehot_a, !(branch_bvalid && trunk_bvalid))

endmodule : br_amba_axil_split
