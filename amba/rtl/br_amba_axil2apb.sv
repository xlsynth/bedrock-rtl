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
    input rst,  // Synchronous active-high

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

  // Internal signals
  logic [AddrWidth-1:0] awaddr_reg, araddr_reg;
  logic [DataWidth-1:0] wdata_reg;
  logic [(DataWidth/8)-1:0] wstrb_reg;
  logic awvalid_reg, wvalid_reg, arvalid_reg;
  logic bready_reg, rready_reg;
  logic [1:0] bresp_reg, rresp_reg;
  logic [DataWidth-1:0] rdata_reg;
  logic bvalid_reg, rvalid_reg;

  // AXI4-Lite write address channel
  always_ff @(posedge clk) begin
    if (rst) begin
      awready <= 1'b0;
      awaddr_reg <= '0;
      awvalid_reg <= 1'b0;
    end else begin
      if (awvalid && !awready) begin
        awready <= 1'b1;
        awaddr_reg <= awaddr;
        awvalid_reg <= 1'b1;
      end else begin
        awready <= 1'b0;
        awvalid_reg <= 1'b0;
      end
    end
  end

  // AXI4-Lite write data channel
  always_ff @(posedge clk) begin
    if (rst) begin
      wready <= 1'b0;
      wdata_reg <= '0;
      wstrb_reg <= '0;
      wvalid_reg <= 1'b0;
    end else begin
      if (wvalid && !wready) begin
        wready <= 1'b1;
        wdata_reg <= wdata;
        wstrb_reg <= wstrb;
        wvalid_reg <= 1'b1;
      end else begin
        wready <= 1'b0;
        wvalid_reg <= 1'b0;
      end
    end
  end

  // AXI4-Lite write response channel
  always_ff @(posedge clk) begin
    if (rst) begin
      bvalid <= 1'b0;
      bresp_reg <= 2'b00;
    end else begin
      if (bready && bvalid) begin
        bvalid <= 1'b0;
      end else if (awvalid_reg && wvalid_reg) begin
        bvalid <= 1'b1;
        bresp_reg <= pslverr ? 2'b10 : 2'b00;
      end
    end
  end

  assign bresp = bresp_reg;

  // AXI4-Lite read address channel
  always_ff @(posedge clk) begin
    if (rst) begin
      arready <= 1'b0;
      araddr_reg <= '0;
      arvalid_reg <= 1'b0;
    end else begin
      if (arvalid && !arready) begin
        arready <= 1'b1;
        araddr_reg <= araddr;
        arvalid_reg <= 1'b1;
      end else begin
        arready <= 1'b0;
        arvalid_reg <= 1'b0;
      end
    end
  end

  // AXI4-Lite read data channel
  always_ff @(posedge clk) begin
    if (rst) begin
      rvalid <= 1'b0;
      rdata_reg <= '0;
      rresp_reg <= 2'b00;
    end else begin
      if (rready && rvalid) begin
        rvalid <= 1'b0;
      end else if (arvalid_reg) begin
        rvalid <= 1'b1;
        rdata_reg <= prdata;
        rresp_reg <= pslverr ? 2'b10 : 2'b00;
      end
    end
  end

  assign rdata = rdata_reg;
  assign rresp = rresp_reg;

  // APB interface control
  always_ff @(posedge clk) begin
    if (rst) begin
      psel <= 1'b0;
      penable <= 1'b0;
      pwrite <= 1'b0;
      paddr <= '0;
      pwdata <= '0;
    end else begin
      if (awvalid_reg && wvalid_reg) begin
        psel <= 1'b1;
        penable <= 1'b1;
        pwrite <= 1'b1;
        paddr <= awaddr_reg;
        pwdata <= wdata_reg;
      end else if (arvalid_reg) begin
        psel <= 1'b1;
        penable <= 1'b1;
        pwrite <= 1'b0;
        paddr <= araddr_reg;
      end else begin
        psel <= 1'b0;
        penable <= 1'b0;
        pwrite <= 1'b0;
      end
    end
  end

endmodule : br_amba_axil2apb
