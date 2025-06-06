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
//
// This module creates MSI messages for a configurable number of interrupts. The
// messages are meant to be compatible with GICv3. The device ID is encoded in
// the address field of the MSI message (4-byte aligned), and the event ID is
// encoded in the lower bits of the data field.
//

// It is expected that the configuration will be done through a register interface
// which is not part of this module.
//
// This module supports high-asserted, level-triggered interrupts. The module
// watches for rising edges of the interrupts and latches them. Then, if enabled,
// it sends the interrupt via the AXI4-Lite initiator interface. It is assumed
// that the interrupt will remain asserted until the interrupt is cleared by SW.
// If the interrupt pulses, a message will be sent again.
//
// This module also supports a per-interrupt enable/disable mechanism. When a
// per-interrupt enable is asserted, the interrupt is sent. When a per-interrupt
// enable is not asserted, the interrupt is not sent.
//
// This module supports a parameterizable number of destination addresses. The
// addresses are input signals. There is a per-interrupt destination index
// which selects which address to use for a given interrupt. The final computed
// address also includes the device ID as a word offset. The user can use device
// ID 0 to not include an offset.
//
// This module also supports a throttle mechanism. When a throttle is enabled,
// the interrupt is sent once every `throttle_cnt` cycles.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_amba_axil_msi #(
    parameter int AddrWidth = 40,  // must be at least 12
    parameter int DataWidth = 64,  // must be 32 or 64
    parameter int NumInterrupts = 2,  // must be at least 2
    parameter int NumMsiDestAddr = 1,  // must be at least 1
    parameter int DeviceIdWidth = 16,  // must be less than or equal to AddrWidth
    parameter int EventIdWidth = 16,  // must be less than or equal to DataWidth
    parameter int ThrottleCntrWidth = 16,  // must be at least 1
    localparam int MsiDstIdxWidth = (NumMsiDestAddr > 1) ? $clog2(NumMsiDestAddr) : 1,
    localparam int StrobeWidth = (DataWidth + 7) / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Interrupt inputs
    input logic [NumInterrupts-1:0] irq,  // synchronous

    // MSI Configuration
    input logic [NumMsiDestAddr-1:0][AddrWidth-1:0] msi_dest_addr,
    input logic [NumInterrupts-1:0] msi_enable,
    input logic [NumInterrupts-1:0][MsiDstIdxWidth-1:0] msi_dest_idx,
    input logic [NumInterrupts-1:0][DeviceIdWidth-1:0] device_id_per_irq,
    input logic [NumInterrupts-1:0][EventIdWidth-1:0] event_id_per_irq,

    // Throttle configuration
    input logic throttle_en,
    input logic [ThrottleCntrWidth-1:0] throttle_cntr_threshold,

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
  `BR_ASSERT_STATIC(data_width_eq_32_or_64_a, (DataWidth == 32) || (DataWidth == 64))
  `BR_ASSERT_STATIC(device_id_lte_addr_width_a, DeviceIdWidth <= AddrWidth)
  `BR_ASSERT_STATIC(event_id_lte_data_width_a, EventIdWidth <= DataWidth)
  `BR_ASSERT_STATIC(num_interrupts_gte_2_a, NumInterrupts >= 2)
  `BR_ASSERT_STATIC(num_msi_dest_addr_gte_1_a, NumMsiDestAddr >= 1)
  `BR_ASSERT_STATIC(throttle_cntr_width_gt_0_a, ThrottleCntrWidth > 0)

  for (genvar i = 0; i < NumInterrupts; i++) begin : gen_num_interrupts_intg_checks
    `BR_ASSERT_INTG(dest_idx_lt_num_msi_dest_addr_a, msi_dest_idx[i] < NumMsiDestAddr)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  localparam int AddrWidthPadding = (AddrWidth - DeviceIdWidth) - 2;  // lower 2 bits are always 00
  localparam int EventIdPadding = 32 - EventIdWidth;  // pad to 32 bits
  localparam int DataWidthPadding = DataWidth - 32;
  localparam int EventIdStrobeWidth = 4;  // always 4 bytes
  localparam int StrobeWidthPadding = StrobeWidth - EventIdStrobeWidth;
  localparam int FlowRegWidth = DeviceIdWidth + EventIdWidth + MsiDstIdxWidth;
  localparam int WriteAddrFlowRegWidth = AddrWidth;
  localparam int WriteDataFlowRegWidth = DataWidth + StrobeWidth;

  logic [NumInterrupts-1:0] irq_d;
  logic [NumInterrupts-1:0] irq_rising_edge;
  logic [NumInterrupts-1:0] pending_irq, pending_irq_next;
  logic [DeviceIdWidth-1:0] device_id_to_send;
  logic [EventIdWidth-1:0] event_id_to_send;
  logic [MsiDstIdxWidth-1:0] irq_dest_idx;
  logic [AddrWidth-1:0] irq_dest_addr;
  logic [NumInterrupts-1:0][FlowRegWidth-1:0] flow_reg_push_data;
  logic [NumInterrupts-1:0] flow_reg_push_ready, flow_reg_push_valid;
  logic [FlowRegWidth-1:0] flow_reg_pop_data;
  logic flow_reg_pop_ready, flow_reg_pop_valid;
  logic error_next;
  logic [ThrottleCntrWidth-1:0] throttle_cntr_value;
  logic throttle_cntr_matches;
  logic reinit_throttle_cntr;
  logic clear_to_send;

  logic write_addr_flow_reg_push_ready, write_addr_flow_reg_push_valid;
  logic [WriteAddrFlowRegWidth-1:0] write_addr_flow_reg_push_data;

  logic write_data_flow_reg_push_ready, write_data_flow_reg_push_valid;
  logic [WriteDataFlowRegWidth-1:0] write_data_flow_reg_push_data;

  // Detect rising edge of irq
  `BR_REG(irq_d, irq)
  assign irq_rising_edge = irq & ~irq_d;

  // Track irqs that are pending to be sent. Set the pending bit when there is a
  // rising edge and clear it when the irq is sent.
  `BR_REG(pending_irq, pending_irq_next)
  assign pending_irq_next =
      msi_enable &
      (pending_irq | irq_rising_edge) &
      ~(flow_reg_push_ready & flow_reg_push_valid);

  // Use round-robin arbitration to select the next irq to send
  br_flow_mux_rr_stable #(
      .RegisterPopReady(1),
      .NumFlows(NumInterrupts),
      .Width(FlowRegWidth)
  ) br_flow_mux_rr_stable (
      .clk,
      .rst,
      .push_ready(flow_reg_push_ready),
      .push_valid(flow_reg_push_valid),
      .push_data (flow_reg_push_data),
      .pop_ready (flow_reg_pop_ready),
      .pop_valid (flow_reg_pop_valid),
      .pop_data  (flow_reg_pop_data)
  );
  generate
    for (genvar i = 0; i < NumInterrupts; i++) begin : gen_loop
      assign flow_reg_push_data[i] = {msi_dest_idx[i], device_id_per_irq[i], event_id_per_irq[i]};
    end
  endgenerate
  assign flow_reg_push_valid = pending_irq;
  assign {irq_dest_idx, device_id_to_send, event_id_to_send} = flow_reg_pop_data;

  // Throttle counter
  br_counter_decr #(
      .MaxValue({ThrottleCntrWidth{1'b1}}),
      .EnableSaturate(1),
      .MaxDecrement(1)
  ) br_counter_decr_throttle (
      .clk,
      .rst,
      .reinit(reinit_throttle_cntr),
      .initial_value(throttle_cntr_threshold),
      .decr_valid(flow_reg_pop_valid),
      .decr(1'b1),
      .value(throttle_cntr_value),
      .value_next()
  );
  assign reinit_throttle_cntr = ~flow_reg_pop_valid || flow_reg_pop_ready;
  assign throttle_cntr_matches = throttle_cntr_value == {ThrottleCntrWidth{1'b0}};
  assign clear_to_send = ~throttle_en || throttle_cntr_matches;

  // Create the data to be pushed into the flow registers
  // ri lint_check_off ZERO_EXT CONST_OUTPUT
  assign irq_dest_addr = msi_dest_addr[irq_dest_idx];  // ri lint_check_waive VAR_INDEX_RANGE
  assign write_addr_flow_reg_push_data = irq_dest_addr +
      {{AddrWidthPadding{1'b0}}, device_id_to_send, 2'b00};
  if (StrobeWidthPadding == 0) begin : gen_no_strb_padding
    assign write_data_flow_reg_push_data = {
      {EventIdPadding{1'b0}}, event_id_to_send, {EventIdStrobeWidth{1'b1}}
    };
  end else begin : gen_strb_padding
    // Need to check the LSB of the device_id_to_send to determine if we need to realign the data
    // and wstrb
    assign write_data_flow_reg_push_data = (device_id_to_send[0] == 1'b0) ? {
      {DataWidthPadding{1'b0}},
      {EventIdPadding{1'b0}},
      event_id_to_send,
      {StrobeWidthPadding{1'b0}},
      {EventIdStrobeWidth{1'b1}}
    } : {
      {EventIdPadding{1'b0}},
      event_id_to_send,
      {DataWidthPadding{1'b0}},
      {EventIdStrobeWidth{1'b1}},
      {StrobeWidthPadding{1'b0}}
    };
  end
  // ri lint_check_on ZERO_EXT CONST_OUTPUT

  // Create the valid/ready signals for the flow registers
  assign write_addr_flow_reg_push_valid = flow_reg_pop_valid && clear_to_send &&
      write_addr_flow_reg_push_ready && write_data_flow_reg_push_ready;
  assign write_data_flow_reg_push_valid = flow_reg_pop_valid && clear_to_send &&
      write_addr_flow_reg_push_ready && write_data_flow_reg_push_ready;
  assign flow_reg_pop_ready = write_addr_flow_reg_push_valid && write_addr_flow_reg_push_ready &&
      write_data_flow_reg_push_valid && write_data_flow_reg_push_ready;

  // Use a flow register to decouple the AXI channels
  br_flow_reg_both #(
      .Width(WriteAddrFlowRegWidth)
  ) br_flow_reg_both_write_addr (
      .clk,
      .rst,

      .push_ready(write_addr_flow_reg_push_ready),
      .push_valid(write_addr_flow_reg_push_valid),
      .push_data (write_addr_flow_reg_push_data),

      .pop_ready(init_awready),
      .pop_valid(init_awvalid),
      .pop_data (init_awaddr)
  );

  // Use a flow register to decouple the AXI channels
  br_flow_reg_both #(
      .Width(WriteDataFlowRegWidth)
  ) br_flow_reg_both_write_data (
      .clk,
      .rst,

      .push_ready(write_data_flow_reg_push_ready),
      .push_valid(write_data_flow_reg_push_valid),
      .push_data (write_data_flow_reg_push_data),

      .pop_ready(init_wready),
      .pop_valid(init_wvalid),
      .pop_data ({init_wdata, init_wstrb})
  );

  // Provide a registered error output
  `BR_REGL(error, error_next, init_bvalid && init_bready)
  assign error_next  = init_bresp != br_amba::AxiRespOkay;  // ri lint_check_waive ENUM_COMPARE

  // No back pressure on the write response channel
  assign init_bready = 1'b1;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT

endmodule : br_amba_axil_msi
