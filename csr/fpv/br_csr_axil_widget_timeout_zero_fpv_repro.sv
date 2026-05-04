// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for timeout_cycles == 0 watchdog behavior.

`include "br_asserts.svh"

module br_csr_axil_widget_timeout_zero_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int AddrWidth = 8;
  localparam int DataWidth = 32;
  localparam int MaxTimeoutCycles = 8;
  localparam int StrobeWidth = DataWidth / 8;
  localparam int TimerWidth = br_math::clamped_clog2(MaxTimeoutCycles + 1);

  logic axil_awvalid;
  logic axil_awready;
  logic [AddrWidth-1:0] axil_awaddr;
  logic [br_amba::AxiProtWidth-1:0] axil_awprot;
  logic axil_wvalid;
  logic axil_wready;
  logic [DataWidth-1:0] axil_wdata;
  logic [StrobeWidth-1:0] axil_wstrb;
  logic axil_bvalid;
  logic axil_bready;
  logic [br_amba::AxiRespWidth-1:0] axil_bresp;
  logic axil_arvalid;
  logic axil_arready;
  logic [AddrWidth-1:0] axil_araddr;
  logic [br_amba::AxiProtWidth-1:0] axil_arprot;
  logic axil_rvalid;
  logic axil_rready;
  logic [DataWidth-1:0] axil_rdata;
  logic [br_amba::AxiRespWidth-1:0] axil_rresp;
  logic csr_req_valid;
  logic csr_req_write;
  logic [AddrWidth-1:0] csr_req_addr;
  logic [DataWidth-1:0] csr_req_wdata;
  logic [StrobeWidth-1:0] csr_req_wstrb;
  logic csr_req_secure;
  logic csr_req_privileged;
  logic csr_req_abort;
  logic csr_resp_valid;
  logic [DataWidth-1:0] csr_resp_rdata;
  logic csr_resp_slverr;
  logic csr_resp_decerr;
  logic [TimerWidth-1:0] timeout_cycles;
  logic request_aborted;

  br_csr_axil_widget #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .MaxTimeoutCycles(MaxTimeoutCycles)
  ) dut (
      .clk,
      .rst,
      .axil_awvalid,
      .axil_awready,
      .axil_awaddr,
      .axil_awprot,
      .axil_wvalid,
      .axil_wready,
      .axil_wdata,
      .axil_wstrb,
      .axil_bvalid,
      .axil_bready,
      .axil_bresp,
      .axil_arvalid,
      .axil_arready,
      .axil_araddr,
      .axil_arprot,
      .axil_rvalid,
      .axil_rready,
      .axil_rdata,
      .axil_rresp,
      .csr_req_valid,
      .csr_req_write,
      .csr_req_addr,
      .csr_req_wdata,
      .csr_req_wstrb,
      .csr_req_secure,
      .csr_req_privileged,
      .csr_req_abort,
      .csr_resp_valid,
      .csr_resp_rdata,
      .csr_resp_slverr,
      .csr_resp_decerr,
      .timeout_cycles,
      .request_aborted
  );

  assign axil_awvalid = 1'b0;
  assign axil_awaddr = '0;
  assign axil_awprot = '0;
  assign axil_wvalid = 1'b0;
  assign axil_wdata = '0;
  assign axil_wstrb = '0;
  assign axil_bready = 1'b1;
  assign axil_arvalid = !rst;
  assign axil_araddr = 8'h20;
  assign axil_arprot = '0;
  assign axil_rready = 1'b1;
  assign csr_resp_valid = 1'b0;
  assign csr_resp_rdata = '0;
  assign csr_resp_slverr = 1'b0;
  assign csr_resp_decerr = 1'b0;
  assign timeout_cycles = '0;

  `BR_ASSERT(timeout_zero_suppresses_abort_a, !rst |-> !csr_req_abort)
  `BR_ASSERT(timeout_zero_suppresses_request_aborted_a, !rst |-> !request_aborted)
  `BR_ASSERT(timeout_zero_suppresses_timeout_response_a, !rst |-> !axil_rvalid)

endmodule : br_csr_axil_widget_timeout_zero_fpv_repro
