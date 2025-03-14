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

// Bedrock-RTL AXI4-Lite MSI Generator

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_msi_fpv_monitor #(
    parameter int AddrWidth = 40,  // must be at least 12
    parameter int DataWidth = 64,  // must be 32 or 64
    parameter int NumInterrupts = 2,  // must be at least 2
    parameter int DeviceIdWidth = 16,  // must be less than or equal to AddrWidth
    parameter int EventIdWidth = 16,  // must be less than or equal to DataWidth
    parameter int ThrottleCntrWidth = 16,  // must be at least 1
    localparam int StrobeWidth = (DataWidth + 7) / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Interrupt inputs
    input logic [NumInterrupts-1:0] irq,

    // MSI Configuration
    input logic [AddrWidth-1:0] msi_base_addr,
    input logic [NumInterrupts-1:0] msi_enable,
    input logic [NumInterrupts-1:0][DeviceIdWidth-1:0] device_id_per_irq,
    input logic [NumInterrupts-1:0][EventIdWidth-1:0] event_id_per_irq,

    // Throttle configuration
    input logic throttle_en,
    input logic [ThrottleCntrWidth-1:0] throttle_cntr_threshold,

    // Error output
    input logic error,

    // AXI4-Lite write-only initiator interface
    input logic [            AddrWidth-1:0] init_awaddr,
    input logic                             init_awvalid,
    input logic                             init_awready,
    input logic [            DataWidth-1:0] init_wdata,
    input logic [          StrobeWidth-1:0] init_wstrb,
    input logic                             init_wvalid,
    input logic                             init_wready,
    input logic [br_amba::AxiRespWidth-1:0] init_bresp,
    input logic                             init_bvalid,
    input logic                             init_bready
);

  // ----------FV modeling code----------
  localparam int AddrWidthPadding = (AddrWidth - DeviceIdWidth) - 2;
  localparam int DataWidthPadding = DataWidth - EventIdWidth;
  localparam int EventIdStrobeWidth = (EventIdWidth + 7) / 8;
  localparam int StrobeWidthPadding = StrobeWidth - EventIdStrobeWidth;

  logic [NumInterrupts-1:0] fv_irp, fv_irp_d, fv_irp_pulse;
  logic [NumInterrupts-1:0][  AddrWidth-1:0] fv_init_awaddr;
  logic [NumInterrupts-1:0][  DataWidth-1:0] fv_init_wdata;
  logic [NumInterrupts-1:0][StrobeWidth-1:0] fv_init_wstrb;

  always_comb begin
    for (int i = 0; i < NumInterrupts; i++) begin
      fv_init_awaddr[i] = msi_base_addr + {{AddrWidthPadding{1'b0}}, device_id_per_irq[i], 2'b00};
      fv_init_wdata[i]  = {{DataWidthPadding{1'b0}}, event_id_per_irq[i]};
      fv_init_wstrb[i]  = {{StrobeWidthPadding{1'b0}}, {EventIdStrobeWidth{1'b1}}};
    end
  end

  assign fv_irp = irq & msi_enable;
  `BR_REG(fv_irp_d, fv_irp)
  assign fv_irp_pulse = fv_irp & ~fv_irp_d;

  // ----------FV assumptions----------
  // TODO
  `BR_ASSUME(throttle_en_stable_a, $stable(throttle_en))
  `BR_ASSUME(throttle_cntr_stable_a, $stable(throttle_cntr_threshold)
             && throttle_cntr_threshold != 'd0)
  `BR_ASSUME(msi_enable_stable_a, $stable(msi_enable))
  `BR_ASSUME(msi_base_addr_stable_a, $stable(msi_base_addr))
  `BR_ASSUME(device_id_stable_a, $stable(device_id_per_irq))
  `BR_ASSUME(event_id_stable_a, $stable(event_id_per_irq))

  // ----------Data integrity Check----------
  /*
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(AddrWidth),
      .IN_CHUNKS(NumInterrupts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(10)
  ) addr_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_irp_pulse),
      .incoming_data(fv_init_awaddr),
      .outgoing_vld(init_awvalid & init_awready & init_wvalid & init_wready),
      .outgoing_data(init_awaddr)
  );*/

  // AXI4-Lite write-only initiator interface
  axi4_slave #(
      .AXI4_LITE (1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth)
  ) axi (
      // Global signals
      .aclk   (clk),
      .aresetn(!rst),
      .csysreq(1'b1),
      .csysack(1'b1),
      .cactive(1'b1),
      // Write Address Channel
      .awvalid(init_awvalid),
      .awready(init_awready),
      .awaddr (init_awaddr),
      .awprot ('d0),
      // Write Channel
      .wvalid (init_wvalid),
      .wready (init_wready),
      .wdata  (init_wdata),
      .wstrb  (init_wstrb),
      // Write Response channel
      .bvalid (init_bvalid),
      .bready (init_bready),
      .bresp  (init_bresp),
      // Read Address Channel
      .arvalid('d0),
      .arready('d0),
      // Read Channel
      .rvalid ('d0),
      .rready ('d0)
  );

endmodule : br_amba_axil_msi_fpv_monitor

bind br_amba_axil_msi br_amba_axil_msi_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .NumInterrupts(NumInterrupts),
    .DeviceIdWidth(DeviceIdWidth),
    .EventIdWidth(EventIdWidth),
    .ThrottleCntrWidth(ThrottleCntrWidth)
) monitor (.*);
