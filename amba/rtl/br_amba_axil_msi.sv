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

// Bedrock-RTL AXI4-Lite MSI Generator
//
// This module creates MSI messages for a configurable number of interrupts. The
// messages are meant to be compatible with GICv3. The device ID is encoded in
// the address field of the MSI message (4-byte aligned), and the event ID is
// encoded in the lower bits of the data field.
//

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_amba_axil_msi #(
    parameter int AddrWidth = 40,  // must be at least 12
    parameter int DataWidth = 64,  // must be at least 32
    parameter int NumInterrupts = 2,  // must be at least 2
    parameter int DeviceIdWidth = 16,  // must be less than or equal to AddrWidth
    parameter int EventIdWidth = 16,  // must be less than or equal to DataWidth
    localparam int StrobeWidth = (DataWidth + 7) / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Interrupt inputs
    input logic [NumInterrupts-1:0] irq,

    // MSI Configuration
    input logic [NumInterrupts-1:0][DeviceIdWidth-1:0] device_id_per_irq,
    input logic [NumInterrupts-1:0][ EventIdWidth-1:0] event_id_per_irq,

    // Error output
    output logic error,

    // AXI4-Lite write-only initiator interface
    output logic [            AddrWidth-1:0] init_awaddr,
    output logic                             init_awvalid,
    input  logic                             init_awready,
    output logic [            DataWidth-1:0] init_wdata,
    output logic [          StrobeWidth-1:0] init_wstrb,
    output logic                             init_wvalid,
    input  logic                             init_wready,
    input  logic [br_amba::AxiRespWidth-1:0] init_bresp,
    input  logic                             init_bvalid,
    output logic                             init_bready
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(addr_width_gte_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_gte_32_a, DataWidth >= 32)
  `BR_ASSERT_STATIC(device_id_lte_addr_width_a, DeviceIdWidth <= AddrWidth)
  `BR_ASSERT_STATIC(event_id_lte_data_width_a, EventIdWidth <= DataWidth)
  `BR_ASSERT_STATIC(num_interrupts_gt_0_a, NumInterrupts > 0)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  localparam int AddrWidthPadding = (AddrWidth - DeviceIdWidth) - 2;  // lower 2 bits are always 00
  localparam int DataWidthPadding = DataWidth - EventIdWidth;
  localparam int EventIdStrobeWidth = (EventIdWidth + 7) / 8;
  localparam int StrobeWidthPadding = StrobeWidth - EventIdStrobeWidth;
  localparam int FifoWidth = DeviceIdWidth + EventIdWidth;

  logic [NumInterrupts-1:0] irq_d;
  logic [NumInterrupts-1:0] irq_rising_edge;
  logic [NumInterrupts-1:0] pending_irq, pending_irq_next;
  logic [DeviceIdWidth-1:0] device_id_to_send;
  logic [EventIdWidth-1:0] event_id_to_send;
  logic [NumInterrupts-1:0][FifoWidth-1:0] fifo_push_data;
  logic [NumInterrupts-1:0] fifo_push_ready, fifo_push_valid;
  logic [FifoWidth-1:0] fifo_pop_data;
  logic fifo_pop_ready, fifo_pop_valid;
  logic error_next;

  // Detect rising edge of irq
  `BR_REG(irq_d, irq)
  assign irq_rising_edge = irq & ~irq_d;

  // Track irqs that are pending to be sent. Set the pending bit when there is a
  // rising edge and clear it when the irq is sent.
  `BR_REG(pending_irq, pending_irq_next)
  assign pending_irq_next = (pending_irq | irq_rising_edge) & ~(fifo_push_ready & fifo_push_valid);

  // Use round-robin arbitration to select the next irq to send
  br_flow_mux_rr #(
      .NumFlows(NumInterrupts),
      .Width(FifoWidth)
  ) br_flow_mux_rr (
      .clk,
      .rst,
      .push_ready(fifo_push_ready),
      .push_valid(fifo_push_valid),
      .push_data (fifo_push_data),
      .pop_ready (fifo_pop_ready),
      .pop_valid (fifo_pop_valid),
      .pop_data  (fifo_pop_data)
  );
  generate
    for (genvar i = 0; i < NumInterrupts; i++) begin : gen_loop
      assign fifo_push_data[i] = {device_id_per_irq[i], event_id_per_irq[i]};
    end
  endgenerate
  assign fifo_push_valid = pending_irq;
  assign {device_id_to_send, event_id_to_send} = fifo_pop_data;


  // AXI4-Lite interface
  assign init_awaddr =  // ri lint_check_waive CONST_OUTPUT
      {
        {AddrWidthPadding{1'b0}}, device_id_to_send, 2'b00
      };
  assign init_wdata =  // ri lint_check_waive CONST_OUTPUT
      {
        {DataWidthPadding{1'b0}}, event_id_to_send
      };
  assign init_wstrb =  // ri lint_check_waive CONST_OUTPUT
      {
        {StrobeWidthPadding{1'b0}}, {EventIdStrobeWidth{1'b1}}
      };
  assign init_awvalid = fifo_pop_valid;
  assign init_wvalid = fifo_pop_valid;
  assign fifo_pop_ready = init_awready && init_wready;

  // Provide a registered error output
  `BR_REGL(error, error_next, init_bvalid && init_bready)
  assign error_next  = init_bresp != br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_COMPARE

  // No back pressure on the write response channel
  assign init_bready = 1'b1;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT

endmodule : br_amba_axil_msi
