// Copyright 2025 The Bedrock-RTL Authors
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
//
// Bedrock-RTL Shared Dynamic Multi-FIFO Push Controller

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_dynamic_push_ctrl #(
    // Number of write ports
    parameter int NumWritePorts = 1,
    // Number of logical FIFOs
    parameter int NumFifos = 2,
    // Total depth of the FIFO
    parameter int Depth = 3,
    // Width of the data
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Push side
    output logic [NumWritePorts-1:0] push_ready,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,

    // Data RAM write ports
    output logic [NumWritePorts-1:0] data_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    output logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    // To Linked List Controllers
    output logic [NumFifos-1:0][NumWritePorts-1:0] next_tail_valid,
    output logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] next_tail,

    // Entry deallocation from pop controller
    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id
);

  // Integration Assertions

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS

  logic [NumWritePorts-1:0][Width+FifoIdWidth-1:0] push_comb_data;

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_push_comb_data
    assign push_comb_data[i] = {push_fifo_id[i], push_data[i]};
  end

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumWritePorts),
      .Width(Width + FifoIdWidth),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg_inst (
      .clk,
      .rst,
      .valid(push_valid),
      .ready(push_ready),
      .data (push_comb_data)
  );

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  // Implementation

  logic [NumWritePorts-1:0] alloc_valid;
  logic [NumWritePorts-1:0] alloc_ready;
  logic [NumWritePorts-1:0][AddrWidth-1:0] alloc_entry_id;

  br_tracker_freelist #(
      .NumEntries(Depth),
      .NumAllocPorts(NumWritePorts),
      .NumDeallocPorts(NumFifos)
  ) br_tracker_freelist_inst (
      .clk,
      .rst,

      .alloc_valid,
      .alloc_ready,
      .alloc_entry_id,

      .dealloc_valid,
      .dealloc_entry_id
  );

  if (NumWritePorts > 1) begin : gen_alloc_mapping
    // Map the allocations to the push ports. Entries are allocated to the freelist
    // staging buffers in a fixed priority, so the lower priority ports may not
    // get entries even if some are free if the FIFO is running nearly full.
    // To have a fair allocation of entries to write ports, we implement a
    // round-robin priority scheme. On a given cycle, the allocation
    // ports are mapped to the write ports starting from the alloc port
    // 0 and progressing to alloc port NumWritePorts-1. The alloc ports
    // get assigned to the active write ports in a priority order,
    // with the lowest priority going to the port that was given the
    // first allocated entry the last time.

    // alloc_mapping[i][j] = 1 if alloc port i is mapped to write port j
    logic [NumWritePorts-1:0][NumWritePorts-1:0] alloc_mapping;
    logic [NumWritePorts-1:0] alloc_lowest_prio;
    logic [NumWritePorts-1:0] alloc_lowest_prio_init;
    logic [NumWritePorts-1:0] alloc_lowest_prio_next;
    logic alloc_prio_update;

    assign alloc_prio_update = |(push_valid & push_ready);
    assign alloc_lowest_prio_init = {1'b1, (NumWritePorts - 1)'(1'b0)};
    assign alloc_lowest_prio_next = alloc_mapping[0];

    `BR_REGLI(alloc_lowest_prio, alloc_lowest_prio_next, alloc_prio_update, alloc_lowest_prio_init)

    // Priority encoder maps lowest active port to alloc port 0,
    // second most active to alloc port 1, etc.
    br_enc_priority_dynamic #(
        .NumRequesters(NumWritePorts),
        .NumResults(NumWritePorts)
    ) br_enc_priority_dynamic_alloc (
        .clk,
        .rst,
        .in(push_valid),
        .lowest_prio(alloc_lowest_prio),
        .out(alloc_mapping)
    );

    for (genvar i = 0; i < NumWritePorts; i++) begin : gen_data_ram_write
      // One-hot select of the alloc ports for this write port.
      logic [NumWritePorts-1:0] alloc_select;

      for (genvar j = 0; j < NumWritePorts; j++) begin : gen_alloc_select
        assign alloc_select[j] = alloc_mapping[j][i];
      end

      assign push_ready[i] = |(alloc_select & alloc_valid);
      assign alloc_ready[i] = |(push_valid & alloc_mapping[i]);

      assign data_ram_wr_valid[i] = push_valid[i] & push_ready[i];
      assign data_ram_wr_data[i] = push_data[i];

      br_mux_onehot #(
          .NumSymbolsIn(NumWritePorts),
          .SymbolWidth (AddrWidth)
      ) br_mux_onehot_data_ram_wr_addr_inst (
          .select(alloc_select),
          .in(alloc_entry_id),
          .out(data_ram_wr_addr[i])
      );
    end
  end else begin : gen_single_alloc
    assign push_ready = alloc_valid;
    assign alloc_ready = push_valid;

    assign data_ram_wr_valid = push_valid & push_ready;
    assign data_ram_wr_addr = alloc_entry_id;
    assign data_ram_wr_data = push_data;
  end

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_next_tail
    logic [NumFifos-1:0] port_next_tail_valid;
    logic [NumFifos-1:0][AddrWidth-1:0] port_next_tail;

    br_demux_bin #(
        .NumSymbolsOut(NumFifos),
        .SymbolWidth  (AddrWidth)
    ) br_demux_bin_port_next_tail_valid_inst (
        .select(push_fifo_id[i]),
        .in_valid(data_ram_wr_valid[i]),
        .in(data_ram_wr_addr[i]),
        .out_valid(port_next_tail_valid),
        .out(port_next_tail)
    );

    for (genvar j = 0; j < NumFifos; j++) begin : gen_fifo_next_tail
      assign next_tail_valid[j][i] = port_next_tail_valid[j];
      assign next_tail[j][i] = port_next_tail[j];
    end
  end

  // Implementation Checks

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  localparam int PortCountWidth = $clog2(NumWritePorts + 1);

  logic [PortCountWidth-1:0] request_count;
  logic [PortCountWidth-1:0] alloc_count;
  logic [PortCountWidth-1:0] grant_count;

  // These are only used for assertions, so it's fine to use $countones
  // ri lint_check_off SYS_TF
  assign request_count = $unsigned($countones(push_valid));
  assign alloc_count   = $unsigned($countones(alloc_valid));
  assign grant_count   = $unsigned($countones(push_valid & push_ready));
  // ri lint_check_on SYS_TF
`endif
`endif

  `BR_ASSERT_IMPL(full_push_acceptance_a,
                  (|push_valid && (alloc_count > request_count)) |-> (request_count == grant_count))
  `BR_ASSERT_IMPL(partial_push_acceptance_a,
                  (|push_valid && (alloc_count < request_count)) |-> (grant_count == alloc_count))

endmodule
