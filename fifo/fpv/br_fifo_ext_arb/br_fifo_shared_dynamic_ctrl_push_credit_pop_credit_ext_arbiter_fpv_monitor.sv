// SPDX-License-Identifier: Apache-2.0

// FPV environment for the shared dynamic credit/credit FIFO controller with an
// external pop arbiter. The shared checker verifies credit safety and per-FIFO
// push-to-pop ordering. External data and pointer RAMs obey fixed-latency,
// read-before-write contracts. Grant legality is assumed only outside system/peer
// reset. Grants may be arbitrary during reset.
// Delayed and indefinitely stalled grants are legal when configured. No fairness
// or request-stability assumption is imposed on the arbiter.

`include "br_asserts.svh"

module br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter_fpv_monitor #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int PopMaxCredits = 1,
    parameter int DataRamReadLatency = 0,
    parameter int PointerRamReadLatency = 0,
    parameter bit ArbiterAlwaysGrants = 1,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int PopCreditWidth = $clog2(PopMaxCredits + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic push_sender_in_reset,
    input logic push_receiver_in_reset,
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

    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic [NumFifos-1:0] pop_credit,
    input logic [NumReadPorts-1:0] pop_valid,
    input logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    input logic [NumReadPorts-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_initial_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_withhold_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_available_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_count_pop,

    // Accepted head pointers reserve credit before the RAM response is delivered.
    input logic [NumFifos-1:0] pop_issue,

    input logic [NumWritePorts-1:0] data_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    input logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,
    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,
    input logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data,
    input logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr,
    input logic [NumReadPorts-1:0] ptr_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data,

    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_request,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant,
    input logic [NumReadPorts-1:0] arb_enable_priority_update
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
  ) fv_checker (
      .rst(fv_rst),
      .system_rst(rst),
      .*
  );

  br_fifo_credit_fpv_ram #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .RamReadLatency(DataRamReadLatency)
  ) fv_data_ram (
      .clk,
      .rst(fv_rst),
      .ram_wr_valid(data_ram_wr_valid),
      .ram_wr_addr(data_ram_wr_addr),
      .ram_wr_data(data_ram_wr_data),
      .ram_rd_addr_valid(data_ram_rd_addr_valid),
      .ram_rd_addr(data_ram_rd_addr),
      .ram_rd_data_valid(data_ram_rd_data_valid),
      .ram_rd_data(data_ram_rd_data)
  );

  br_fifo_credit_fpv_ram #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(AddrWidth),
      .RamReadLatency(PointerRamReadLatency)
  ) fv_ptr_ram (
      .clk,
      .rst(fv_rst),
      .ram_wr_valid(ptr_ram_wr_valid),
      .ram_wr_addr(ptr_ram_wr_addr),
      .ram_wr_data(ptr_ram_wr_data),
      .ram_rd_addr_valid(ptr_ram_rd_addr_valid),
      .ram_rd_addr(ptr_ram_rd_addr),
      .ram_rd_data_valid(ptr_ram_rd_data_valid),
      .ram_rd_data(ptr_ram_rd_data)
  );

  for (genvar r = 0; r < NumReadPorts; r++) begin : gen_arbiter
    `BR_ASSUME_CR(arb_grant_onehot_a, $onehot0(arb_grant[r]), clk, fv_rst)
    `BR_ASSUME_CR(arb_grant_requested_a, (arb_grant[r] & ~arb_request[r]) == '0, clk, fv_rst)
    if (ArbiterAlwaysGrants) begin : gen_always_grants
      `BR_ASSUME_CR(arb_always_grants_a, |arb_request[r] |-> |arb_grant[r], clk, fv_rst)
    end else begin : gen_can_stall
      `BR_COVER(arb_stall_then_grant_c,
                !fv_rst && |arb_request[r] && !(|arb_grant[r])
                ##1 !fv_rst && |arb_request[r] && |arb_grant[r])
    end

    `BR_ASSERT(arb_priority_update_enabled_a, !fv_rst |-> arb_enable_priority_update[r])
    `BR_ASSERT(arb_grant_issues_read_a, !fv_rst |-> data_ram_rd_addr_valid[r] == (|arb_grant[r]))
    `BR_COVER(arb_contention_c, !fv_rst && !$onehot0(arb_request[r]))
    `BR_COVER(pop_on_port_c, !fv_rst && pop_valid[r])
  end

  for (genvar f = 0; f < NumFifos; f++) begin : gen_fifo
    logic [NumReadPorts-1:0] fifo_grants;
    for (genvar r = 0; r < NumReadPorts; r++) begin : gen_read_port
      assign fifo_grants[r] = arb_grant[r][f];
    end
    `BR_ASSERT(fifo_granted_at_most_once_a, !fv_rst |-> $onehot0(fifo_grants))
    `BR_ASSERT(grant_matches_pop_issue_a, !fv_rst |-> pop_issue[f] == (|fifo_grants))
  end

endmodule : br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter_fpv_monitor

bind br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter
    br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter_fpv_monitor #(
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .PopMaxCredits(PopMaxCredits),
    .DataRamReadLatency(DataRamReadLatency),
    .PointerRamReadLatency(PointerRamReadLatency),
    .ArbiterAlwaysGrants(ArbiterAlwaysGrants)
) monitor (
    .pop_issue(head_valid & head_ready),
    .*
);
