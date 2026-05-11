// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pop_ctrl_common_fpv_checker #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit RegisterDeallocation = 0,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int FifoIdxWidth = (NumFifos <= 1) ? 1 : $clog2(NumFifos)
) (
    input logic clk,
    input logic rst,

    input logic [FifoIdxWidth-1:0] fv_fifo_id,
    output logic [NumFifos-1:0] head_hs,
    output logic [NumReadPorts-1:0][FifoIdxWidth-1:0] rd_fifo_id,
    output logic [NumReadPorts-1:0] fv_rsp_valid,

    input logic [NumFifos-1:0] head_valid,
    input logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,

    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid
);

  assign head_hs = head_valid & head_ready;

  always_comb begin
    rd_fifo_id = '0;
    for (int p = 0; p < NumReadPorts; p++) begin
      for (int f = 0; f < NumFifos; f++) begin
        if (data_ram_rd_addr_valid[p] && head_hs[f] && (data_ram_rd_addr[p] == head[f])) begin
          rd_fifo_id[p] = FifoIdxWidth'(f);
        end
      end
    end
  end

  // The symbolic FIFO selection lets one scoreboard prove per-FIFO data ordering.
  `BR_ASSUME(fv_fifo_id_range_a, $stable(fv_fifo_id) && (fv_fifo_id < NumFifos))

  for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo
    logic head_has_read_addr;

    always_comb begin
      head_has_read_addr = 1'b0;
      for (int p = 0; p < NumReadPorts; p++) begin
        head_has_read_addr |= data_ram_rd_addr_valid[p] && (data_ram_rd_addr[p] == head[i]);
      end
    end

    // Pointer management must not offer a head pointer for an empty logical FIFO.
    `BR_ASSUME(no_head_when_ram_empty_a, ram_empty[i] |-> !head_valid[i])

    // Every accepted head pointer must issue exactly as a shared RAM read request.
    `BR_ASSERT(accepted_head_has_read_a, head_hs[i] |-> head_has_read_addr)

    // Exercise the deallocation path for every logical FIFO.
    `BR_COVER(dealloc_valid_c, dealloc_valid[i])
  end

  for (genvar i = 0; i < NumFifos; i++) begin : gen_unique_heads_i
    for (genvar j = i + 1; j < NumFifos; j++) begin : gen_unique_heads_j
      // Shared FIFO storage must not present the same allocated entry as two FIFO heads.
      `BR_ASSUME(unique_accepted_heads_a, !head_hs[i] || !head_hs[j] || (head[i] != head[j]))
    end
  end

  for (genvar p = 0; p < NumReadPorts; p++) begin : gen_read_port_checks
    logic rd_addr_matches_accepted_head;

    always_comb begin
      rd_addr_matches_accepted_head = 1'b0;
      for (int f = 0; f < NumFifos; f++) begin
        rd_addr_matches_accepted_head |= head_hs[f] && (data_ram_rd_addr[p] == head[f]);
      end
    end

    // Each read request must come from a head pointer accepted in the same cycle.
    `BR_ASSERT(read_addr_from_head_a, data_ram_rd_addr_valid[p] |-> rd_addr_matches_accepted_head)

    if (RamReadLatency == 0) begin : gen_lat0
      assign fv_rsp_valid[p] = data_ram_rd_data_valid[p] && (rd_fifo_id[p] == fv_fifo_id);

      // The external RAM response valid must match the same-cycle read request.
      `BR_ASSUME(ram_response_valid_latency_a,
                 data_ram_rd_data_valid[p] == data_ram_rd_addr_valid[p])
    end else begin : gen_lat_non0
      logic fv_rsp_fifo_match;

      fv_delay #(
          .Width(1),
          .NumStages(RamReadLatency)
      ) fv_delay_rsp_fifo_match (
          .clk,
          .rst,
          .in (rd_fifo_id[p] == fv_fifo_id),
          .out(fv_rsp_fifo_match)
      );

      assign fv_rsp_valid[p] = data_ram_rd_data_valid[p] && fv_rsp_fifo_match;

      // No RAM response may appear until a post-reset read can mature.
      `BR_ASSUME(no_ram_response_after_reset_a,
                 $fell(rst) |-> !data_ram_rd_data_valid[p] [* RamReadLatency])

      // The external RAM response valid must match the configured delayed read request.
      `BR_ASSUME(ram_response_valid_latency_a,
                 ##RamReadLatency data_ram_rd_data_valid[p] == $past(
                     data_ram_rd_addr_valid[p], RamReadLatency
                 ))
    end

    // Exercise every shared RAM read port.
    `BR_COVER(read_port_valid_c, data_ram_rd_addr_valid[p])
  end

  // The number of accepted heads and read requests must match cycle-by-cycle.
  `BR_ASSERT(read_count_matches_head_hs_a, $countones(data_ram_rd_addr_valid) == $countones(head_hs
                                                                                               ))

  // The pop side can accept at most one head per physical read port per cycle.
  `BR_ASSERT(head_hs_read_port_capacity_a, $countones(head_hs) <= NumReadPorts)

  if (RegisterDeallocation) begin : gen_registered_deallocation_check
    logic [NumFifos-1:0] expected_dealloc_valid_q;

    `BR_REG(expected_dealloc_valid_q, head_hs)

    // Registered deallocation valid must be the previous accepted-head vector.
    `BR_ASSERT(dealloc_valid_registered_a, dealloc_valid == expected_dealloc_valid_q)

    for (genvar i = 0; i < NumFifos; i++) begin : gen_dealloc_entry_checks
      // Registered deallocation entry ID must name the previously accepted head entry.
      `BR_ASSERT(dealloc_entry_id_a, ##1 dealloc_valid[i] |-> dealloc_entry_id[i] == $past(head[i]))
    end
  end else begin : gen_unregistered_deallocation_check
    // Unregistered deallocation valid must match the accepted-head vector immediately.
    `BR_ASSERT(dealloc_valid_unregistered_a, dealloc_valid == head_hs)

    for (genvar i = 0; i < NumFifos; i++) begin : gen_dealloc_entry_checks
      // Unregistered deallocation entry ID must name the same-cycle accepted head entry.
      `BR_ASSERT(dealloc_entry_id_a, dealloc_valid[i] |-> dealloc_entry_id[i] == head[i])
    end
  end

  if (NumReadPorts < NumFifos) begin : gen_read_contention_cover
    // Exercise read-port contention when the configuration has fewer read ports than FIFOs.
    `BR_COVER(read_contention_c, $countones(head_valid) > NumReadPorts)
  end

  // Exercise a cycle where the controller uses all available read ports.
  `BR_COVER(all_read_ports_used_c, &data_ram_rd_addr_valid)

endmodule : br_fifo_shared_pop_ctrl_common_fpv_checker
