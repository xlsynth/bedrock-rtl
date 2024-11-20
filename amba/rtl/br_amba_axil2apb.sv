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
    output logic [AddrWidth-1:0] paddr,
    output logic                 psel,
    output logic                 penable,
    output logic                 pwrite,
    output logic [DataWidth-1:0] pwdata,
    input  logic [DataWidth-1:0] prdata,
    input  logic                 pready,
    input  logic                 pslverr
);

  typedef enum logic [1:0] {
    IDLE,
    SETUP,
    ACCESS
  } apb_state_t;
  apb_state_t apb_state, apb_state_next;

  logic [AddrWidth-1:0] addr_reg;
  logic [DataWidth-1:0] data_reg;
  logic write_reg;
  logic write_txn, read_txn;
  logic write_done, read_done;

  // APB signal assignments
  assign psel = (apb_state != IDLE);
  assign penable = (apb_state == ACCESS);

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      // Reset APB signals
      apb_state <= IDLE;
      addr_reg  <= '0;
      data_reg  <= '0;
      write_reg <= 1'b0;
    end else begin
      apb_state <= apb_state_next;

      if (write_txn || read_txn) begin
        addr_reg  <= write_txn ? awaddr : araddr;
        data_reg  <= wdata;
        write_reg <= write_txn;
      end
    end
  end

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
          apb_state_next = IDLE;
        end
      end
    endcase
  end

  // Write transaction detection
  assign write_txn = awvalid && wvalid && ~bvalid && (apb_state == IDLE);
  assign write_done = bvalid && bready;

  // Read transaction detection
  assign read_txn = arvalid && ~rvalid && (apb_state == IDLE);
  assign read_done = rvalid && rready;

  // AXI4-Lite write handshake
  assign awready = (apb_state == IDLE);
  assign wready = (apb_state == IDLE);
  assign bvalid = write_done;
  assign bresp = pslverr ? 2'b10 : 2'b00;  // Error or OKAY

  // AXI4-Lite read handshake
  assign arready = (apb_state == IDLE);
  assign rvalid = (apb_state == IDLE) && read_done;
  assign rresp = pslverr ? 2'b10 : 2'b00;  // Error or OKAY

  always_ff @(posedge clk) begin
    if (rst) begin
      rdata <= '0;
    end else if (read_done) begin
      rdata <= prdata;
    end
  end

  // APB signal generation
  assign paddr  = addr_reg;
  assign pwdata = data_reg;
  assign pwrite = write_reg;

endmodule : br_amba_axil2apb
