// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for normalized branch address stability under downstream
// backpressure.

import br_amba::*;

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_split_branch_addr_stability_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int AddrWidth = 12;
  localparam int DataWidth = 32;
  localparam int UserWidth = 1;
  localparam int StrobeWidth = DataWidth / 8;

  logic [1:0] cycle;
  logic [0:0][AddrWidth-1:0] branch_start_addr;
  logic [0:0][AddrWidth-1:0] branch_end_addr;
  logic [AddrWidth-1:0] branch_araddr;
  logic [AxiProtWidth-1:0] branch_arprot;
  logic [UserWidth-1:0] branch_aruser;
  logic branch_arvalid;
  logic branch_arready;

  br_amba_axil_split #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .AWUserWidth(UserWidth),
      .WUserWidth(UserWidth),
      .ARUserWidth(UserWidth),
      .RUserWidth(UserWidth),
      .MaxOutstandingReads(1),
      .MaxOutstandingWrites(1),
      .NumBranchAddrRanges(1),
      .NormalizeBranchAddress(1)
  ) dut (
      .clk,
      .rst,
      .branch_start_addr,
      .branch_end_addr,
      .root_awaddr('0),
      .root_awprot('0),
      .root_awuser('0),
      .root_awvalid(1'b0),
      .root_awready(),
      .root_wdata('0),
      .root_wstrb('0),
      .root_wuser('0),
      .root_wvalid(1'b0),
      .root_wready(),
      .root_bresp(),
      .root_bvalid(),
      .root_bready(1'b1),
      .root_araddr(12'h120),
      .root_arprot('0),
      .root_aruser('0),
      .root_arvalid(!rst),
      .root_arready(),
      .root_rdata(),
      .root_rresp(),
      .root_ruser(),
      .root_rvalid(),
      .root_rready(1'b1),
      .trunk_awaddr(),
      .trunk_awprot(),
      .trunk_awuser(),
      .trunk_awvalid(),
      .trunk_awready(1'b1),
      .trunk_wdata(),
      .trunk_wstrb(),
      .trunk_wuser(),
      .trunk_wvalid(),
      .trunk_wready(1'b1),
      .trunk_bresp(AxiRespOkay),
      .trunk_bvalid(1'b0),
      .trunk_bready(),
      .trunk_araddr(),
      .trunk_arprot(),
      .trunk_aruser(),
      .trunk_arvalid(),
      .trunk_arready(1'b1),
      .trunk_rdata('0),
      .trunk_rresp(AxiRespOkay),
      .trunk_ruser('0),
      .trunk_rvalid(1'b0),
      .trunk_rready(),
      .branch_awaddr(),
      .branch_awprot(),
      .branch_awuser(),
      .branch_awvalid(),
      .branch_awready(1'b1),
      .branch_wdata(),
      .branch_wstrb(),
      .branch_wuser(),
      .branch_wvalid(),
      .branch_wready(1'b1),
      .branch_bresp(AxiRespOkay),
      .branch_bvalid(1'b0),
      .branch_bready(),
      .branch_araddr,
      .branch_arprot,
      .branch_aruser,
      .branch_arvalid,
      .branch_arready,
      .branch_rdata('0),
      .branch_rresp(AxiRespOkay),
      .branch_ruser('0),
      .branch_rvalid(1'b0),
      .branch_rready()
  );

  assign branch_start_addr[0] = cycle == 0 ? 12'h100 : 12'h110;
  assign branch_end_addr[0] = 12'h1ff;
  assign branch_arready = 1'b0;

  `BR_REG(cycle, cycle + 2'd1)

  `BR_ASSERT(branch_araddr_stable_a,
             branch_arvalid && !branch_arready |=> $stable(branch_araddr))

endmodule : br_amba_axil_split_branch_addr_stability_fpv_repro
