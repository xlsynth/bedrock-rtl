// SPDX-License-Identifier: Apache-2.0

// FPV monitor for br_fifo_shared_dynamic_flops_push_credit_pop_credit.
// The controller uses fixed-latency external RAM models; the flops variant
// checks the instantiated storage directly. See the shared checker for the
// input protocol and the distinct read-issue / response boundaries.

`include "br_asserts.svh"

module br_fifo_shared_dynamic_flops_push_credit_pop_credit_fpv_monitor #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int PopMaxCredits = 1,
    parameter bit RegisterPushOutputs = 0,
    parameter int DataRamReadLatency = 0,
    parameter int PointerRamReadLatency = 0,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int PopCreditWidth = $clog2(PopMaxCredits + 1),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,
    input logic push_sender_in_reset,
    input logic push_receiver_in_reset,
    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic push_credit_stall,
    input logic [PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    input logic push_full,
    input logic [CountWidth-1:0] credit_initial_push,
    input logic [CountWidth-1:0] credit_withhold_push,
    input logic [CountWidth-1:0] credit_available_push,
    input logic [CountWidth-1:0] credit_count_push,
    input logic [NumFifos-1:0] pop_credit,
    input logic [NumReadPorts-1:0] pop_valid,
    input logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    input logic [NumReadPorts-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_initial_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_withhold_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_available_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_count_pop,
    input logic [NumFifos-1:0] pop_issue
);

  logic fv_rst;
  assign fv_rst = rst || push_sender_in_reset || pop_receiver_in_reset;

  br_fifo_shared_dynamic_credit_fpv_checker #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .PopMaxCredits(PopMaxCredits),
      .DataRamReadLatency(DataRamReadLatency)
  ) checker_inst (
      .rst(fv_rst),
      .*
  );

  `BR_ASSERT_INCL_RST(pop_reset_interface_a, pop_sender_in_reset == (rst || push_sender_in_reset))
  if (RegisterPushOutputs) begin : gen_registered_reset
    `BR_ASSERT_INCL_RST(push_reset_interface_a,
                        ##1 push_receiver_in_reset == $past(rst || pop_receiver_in_reset))
  end else begin : gen_combinational_reset
    `BR_ASSERT_INCL_RST(push_reset_interface_a,
                        push_receiver_in_reset == (rst || pop_receiver_in_reset))
  end

endmodule : br_fifo_shared_dynamic_flops_push_credit_pop_credit_fpv_monitor

bind br_fifo_shared_dynamic_flops_push_credit_pop_credit
    br_fifo_shared_dynamic_flops_push_credit_pop_credit_fpv_monitor #(
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .PopMaxCredits(PopMaxCredits),
    .RegisterPushOutputs(RegisterPushOutputs),
    .DataRamReadLatency(DataRamReadLatency),
    .PointerRamReadLatency(PointerRamReadLatency)
) monitor (
    .pop_issue(br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_inst.head_valid &
        br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_inst.head_ready),
    .*
);
