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

// Bridge AXI4-Lite to APB Bridge
//
// Converts an AXI4-Lite interface to an APB interface.

`include "br_registers.svh"

module br_amba_axil2apb #(
    parameter int AddrWidth = 40,
    parameter int DataWidth = 64
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite interface
    input  logic [    AddrWidth-1:0] awaddr,
    input  logic [              2:0] awprot,
    input  logic                     awvalid,
    output logic                     awready,
    input  logic [    DataWidth-1:0] wdata,
    input  logic [(DataWidth/8)-1:0] wstrb,
    input  logic                     wvalid,
    output logic                     wready,
    output logic [              1:0] bresp,
    output logic                     bvalid,
    input  logic                     bready,
    input  logic [    AddrWidth-1:0] araddr,
    input  logic [              2:0] arprot,
    input  logic                     arvalid,
    output logic                     arready,
    output logic [    DataWidth-1:0] rdata,
    output logic [              1:0] rresp,
    output logic                     rvalid,
    input  logic                     rready,

    // APB interface
    output logic [    AddrWidth-1:0] paddr,
    output logic                     psel,
    output logic                     penable,
    output logic [              2:0] pprot,
    output logic [(DataWidth/8)-1:0] pstrb,
    output logic                     pwrite,
    output logic [    DataWidth-1:0] pwdata,
    input  logic [    DataWidth-1:0] prdata,
    input  logic                     pready,
    input  logic                     pslverr
);

  typedef enum logic [2:0] {
    IDLE   = 3'b001,
    SETUP  = 3'b010,
    ACCESS = 3'b100
  } apb_state_t;
  apb_state_t apb_state, apb_state_next;

  logic [AddrWidth-1:0] addr_reg, addr_next;
  logic [DataWidth-1:0] data_reg;
  logic [(DataWidth/8)-1:0] strb_reg;
  logic [2:0] prot_reg, prot_next;
  logic write_reg;
  logic write_txn, write_txn_next;
  logic read_txn, read_txn_next;
  logic read_or_write_txn;
  logic write_done, write_done_next;
  logic read_done, read_done_next;

  `BR_REGLN(addr_reg, addr_next, read_or_write_txn)
  `BR_REGLN(data_reg, wdata, read_or_write_txn)
  `BR_REGLN(write_reg, write_txn, read_or_write_txn)
  `BR_REGLN(strb_reg, wstrb, read_or_write_txn)
  `BR_REGLN(prot_reg, prot_next, read_or_write_txn)
  `BR_REGLN(rdata, prdata, read_done)
  `BR_REG(write_txn, write_txn_next)
  `BR_REG(read_txn, read_txn_next)
  `BR_REG(write_done, write_done_next)
  `BR_REG(read_done, read_done_next)
  `BR_REGI(apb_state, apb_state_next, IDLE)

  // Transaction control
  assign addr_next = write_txn ? awaddr : araddr;
  assign prot_next = write_txn ? awprot : arprot;
  assign read_or_write_txn = write_txn || read_txn;
  assign write_txn_next = awvalid && wvalid && ~bvalid && (apb_state == IDLE);
  assign read_txn_next = arvalid && ~rvalid && (apb_state == IDLE);
  assign write_done_next = bvalid && bready;
  assign read_done_next = rvalid && rready;

  // APB state machine
  // ri lint_check_off GRAY_CODE_FSM
  always_comb begin
    // Default next state
    apb_state_next = apb_state;

    unique case (apb_state)
      IDLE: begin
        if (write_txn || read_txn) begin
          apb_state_next = SETUP;
        end
      end
      SETUP: begin
        apb_state_next = ACCESS;
      end
      ACCESS: begin
        if (pready) begin
          apb_state_next = IDLE;  // ri lint_check_waive GRAY_CODE_FSM
        end
      end
      default: begin
        apb_state_next = IDLE;
      end
    endcase
  end
  // ri lint_check_on GRAY_CODE_FSM

  // AXI4-Lite signal generation
  assign awready = (apb_state == IDLE);
  assign wready = (apb_state == IDLE);
  assign bvalid = write_done;
  assign bresp = pslverr ? 2'b10 : 2'b00;  // ri lint_check_waive CONST_OUTPUT
  assign arready = (apb_state == IDLE);
  assign rvalid = (apb_state == IDLE) && read_done;
  assign rresp = pslverr ? 2'b10 : 2'b00;  // ri lint_check_waive CONST_OUTPUT

  // APB signal generation
  assign psel = (apb_state != IDLE);
  assign penable = (apb_state == ACCESS);
  assign paddr = addr_reg;
  assign pwdata = data_reg;
  assign pwrite = write_reg;
  assign pprot = prot_reg;
  assign pstrb = strb_reg;

endmodule : br_amba_axil2apb
