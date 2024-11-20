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

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_amba_axil2apb #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32   // Must be at least 32
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite interface
    input  logic [            AddrWidth-1:0] awaddr,
    input  logic [br_amba::AxiProtWidth-1:0] awprot,
    input  logic                             awvalid,
    output logic                             awready,
    input  logic [            DataWidth-1:0] wdata,
    input  logic [        (DataWidth/8)-1:0] wstrb,
    input  logic                             wvalid,
    output logic                             wready,
    output logic [br_amba::AxiRespWidth-1:0] bresp,
    output logic                             bvalid,
    input  logic                             bready,
    input  logic [            AddrWidth-1:0] araddr,
    input  logic [br_amba::AxiProtWidth-1:0] arprot,
    input  logic                             arvalid,
    output logic                             arready,
    output logic [            DataWidth-1:0] rdata,
    output logic [br_amba::AxiRespWidth-1:0] rresp,
    output logic                             rvalid,
    input  logic                             rready,

    // APB interface
    output logic [            AddrWidth-1:0] paddr,
    output logic                             psel,
    output logic                             penable,
    output logic [br_amba::ApbProtWidth-1:0] pprot,
    output logic [        (DataWidth/8)-1:0] pstrb,
    output logic                             pwrite,
    output logic [            DataWidth-1:0] pwdata,
    input  logic [            DataWidth-1:0] prdata,
    input  logic                             pready,
    input  logic                             pslverr
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_at_least_32_a, DataWidth >= 32)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  typedef enum logic [3:0] {
    Idle   = 4'b0001,
    Setup  = 4'b0010,
    Access = 4'b0100,
    Resp   = 4'b1000
  } apb_state_t;
  apb_state_t apb_state, apb_state_next;

  logic [AddrWidth-1:0] addr_reg, addr_next;
  logic [DataWidth-1:0] data_reg;
  logic [(DataWidth/8)-1:0] strb_reg;
  logic [br_amba::AxiProtWidth-1:0] prot_reg, prot_next;
  logic resp_reg;
  logic write_reg;
  logic arb_write_req, arb_write_grant;
  logic arb_read_req, arb_read_grant;
  logic arb_any_grant;

  `BR_REGLN(addr_reg, addr_next, arb_any_grant)
  `BR_REGLN(data_reg, wdata, arb_any_grant)
  `BR_REGLN(write_reg, arb_write_grant, arb_any_grant)
  `BR_REGLN(strb_reg, wstrb, arb_any_grant)
  `BR_REGLN(prot_reg, prot_next, arb_any_grant)
  `BR_REGLN(resp_reg, pslverr, (apb_state == Access) && pready)
  `BR_REGLN(rdata, prdata, (apb_state == Access) && pready)
  `BR_REGI(apb_state, apb_state_next, Idle)

  // Arbitrate between read and write transactions
  br_arb_rr #(
      .NumRequesters(2)
  ) br_arb_rr (
      .clk(clk),
      .rst(rst),
      .enable_priority_update(1'b0),
      .request({arb_write_req, arb_read_req}),
      .grant({arb_write_grant, arb_read_grant})
  );

  // Arbiter request signals
  assign arb_write_req = awvalid && wvalid && (apb_state == Idle);
  assign arb_read_req = arvalid && (apb_state == Idle);
  assign arb_any_grant = arb_write_grant || arb_read_grant;

  // Save the address and data for the transaction
  assign addr_next = arb_write_grant ? awaddr : araddr;
  assign prot_next = arb_write_grant ? awprot : arprot;

  // APB state machine
  // ri lint_check_off GRAY_CODE_FSM
  always_comb begin
    // Default next state
    apb_state_next = apb_state;

    unique case (apb_state)  // ri lint_check_waive FSM_DEFAULT_REQ
      Idle: begin
        if (arb_any_grant) begin
          apb_state_next = Setup;
        end
      end
      Setup: begin
        apb_state_next = Access;
      end
      Access: begin
        if (pready) begin
          apb_state_next = Resp;
        end
      end
      Resp: begin
        if ((write_reg && bready) || (!write_reg && rready)) begin
          apb_state_next = Idle;
        end
      end
    endcase
  end
  // ri lint_check_on GRAY_CODE_FSM

  // AXI4-Lite signal generation
  assign awready = arb_write_grant;
  assign wready = arb_write_grant;
  assign bvalid = (apb_state == Resp) && write_reg;
  assign bresp = resp_reg ? br_amba::AxiRespSlverr : br_amba::AxiRespOkay;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT ENUM_RHS
  assign arready = arb_read_grant;
  assign rvalid = (apb_state == Resp) && ~write_reg;
  assign rresp = resp_reg ? br_amba::AxiRespSlverr : br_amba::AxiRespOkay;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT ENUM_RHS

  // APB signal generation
  assign psel = (apb_state == Setup) || (apb_state == Access);
  assign penable = (apb_state == Access);
  assign paddr = addr_reg;
  assign pwdata = data_reg;
  assign pwrite = write_reg;
  assign pprot = prot_reg;
  assign pstrb = strb_reg;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  `BR_ASSERT_IMPL(apb_state_next_known_a, $isknown(apb_state))

endmodule : br_amba_axil2apb
