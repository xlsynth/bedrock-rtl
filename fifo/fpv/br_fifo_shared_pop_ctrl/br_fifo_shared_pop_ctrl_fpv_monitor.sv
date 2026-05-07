// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Shared Multi-FIFO Pop Controller FPV monitor
//
// Testplan
//
// Design intent:
// - Manage the pop side of a shared multi-FIFO whose storage, FIFO head pointers, and
//   per-FIFO item counts are provided by surrounding controller logic.
// - Accept a head pointer from a logical FIFO when that FIFO has storage-backed items
//   available and the pop-side read path can accept a refill request.
// - Issue data RAM read addresses through NumReadPorts shared read ports using the
//   built-in LRU arbitration policy.
// - Return RAM read data to the selected FIFO pop interface through direct cut-through
//   logic when there is no staging buffer, or through a per-FIFO staging buffer when RAM
//   read latency or registered pop outputs require buffering.
// - Generate deallocation information for entries whose head pointer has been accepted,
//   optionally registering the deallocation path.
//
// Input assumptions to model in a full monitor implementation:
// - Parameter values are legal: NumReadPorts is at least 1 and a power of 2, NumFifos is
//   at least 1, Depth and Width are nonzero, StagingBufferDepth is nonzero, and
//   RamReadLatency is nonnegative.
// - The external pointer manager only asserts head_valid for FIFOs that are nonempty.
// - head remains stable while head_valid is asserted and head_ready is deasserted.
// - data_ram_rd_data_valid/data_ram_rd_data follow the issued read address stream with
//   the configured RamReadLatency.
// - pop_ready obeys the no-staging-buffer integration constraint: when there is no
//   staging buffer, pop_ready holds high while waiting for pop_valid.
//
// Output behavior to check in a full monitor implementation:
// - head_ready only accepts head pointers when the corresponding read/staging path can
//   consume them.
// - data_ram_rd_addr_valid/data_ram_rd_addr correspond to accepted head pointers.
// - pop_valid/pop_data preserve per-FIFO read data ordering and valid-ready stability.
// - pop_empty reflects the empty state of the external RAM plus any staged pop-side data.
// - dealloc_valid/dealloc_entry_id correspond exactly to accepted head pointers, with the
//   configured RegisterDeallocation timing.
// - The built-in LRU arbitration does not issue more than one request per read port and
//   makes bounded progress under sustained requests.
//
// Covers to add in a full monitor implementation:
// - Multiple FIFOs contend for fewer read ports than FIFOs.
// - Each read port issues a RAM read.
// - Each FIFO produces pop data after a staged RAM read.
// - Registered and unregistered deallocation paths both retire entries.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pop_ctrl_fpv_monitor #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterDeallocation = 0,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    input logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,
    input logic [NumFifos-1:0][CountWidth-1:0] ram_items,

    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,

    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);
  localparam bit HasStagingBuffer = (RamReadLatency > 0) || RegisterPopOutputs;
  localparam int FifoIdxWidth = (NumFifos <= 1) ? 1 : $clog2(NumFifos);
  localparam int MaxPending = Depth + StagingBufferDepth + (NumReadPorts * (RamReadLatency + 1));

  logic [NumFifos-1:0] head_hs;
  logic [NumReadPorts-1:0][FifoIdxWidth-1:0] rd_fifo_id;
  logic [FifoIdxWidth-1:0] fv_fifo_id;
  logic [NumReadPorts-1:0] fv_rsp_valid;

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
    // Pointer management must not offer a head pointer for an empty logical FIFO.
    `BR_ASSUME(no_head_when_ram_empty_a, ram_empty[i] |-> !head_valid[i])

    // The external item count must stay inside the configured storage capacity.
    `BR_ASSUME(ram_items_in_range_a, ram_items[i] <= CountWidth'(Depth))

    // The external empty flag must agree with the external item count abstraction.
    `BR_ASSUME(ram_empty_matches_items_a, ram_empty[i] == (ram_items[i] == '0))

    // This isolated pop-controller environment has no write side, so accepted heads consume RAM items.
    `BR_ASSUME(ram_items_decrement_on_head_hs_a,
               ##1 ram_items[i] == ($past(
                   head_hs[i]
               ) ? ($past(
                   ram_items[i]
               ) - CountWidth'(1'b1)) : $past(
                   ram_items[i]
               )))

    // Downstream pop consumers must eventually make progress so staged data can drain.
    `BR_ASSUME(pop_ready_liveness_a, s_eventually pop_ready[i])

    // The head pointer source uses ready/valid semantics, so payload holds under backpressure.
    fv_valid_ready_check #(
        .Master(1),
        .PayloadWidth(AddrWidth)
    ) fv_head_valid_ready_check (
        .clk,
        .rst,
        .ready  (head_ready[i]),
        .valid  (head_valid[i]),
        .payload(head[i])
    );

    if (HasStagingBuffer) begin : gen_pop_valid_ready_check
      // The staged pop interface is a DUT ready/valid output and must hold under backpressure.
      fv_valid_ready_check #(
          .Master(0),
          .PayloadWidth(Width)
      ) fv_pop_valid_ready_check (
          .clk,
          .rst,
          .ready  (pop_ready[i]),
          .valid  (pop_valid[i]),
          .payload(pop_data[i])
      );
    end

    // A FIFO cannot report empty in the same cycle that it presents valid pop data.
    `BR_ASSERT(pop_empty_consistent_a, pop_valid[i] |-> !pop_empty[i])

    // Exercise the pop interface for every logical FIFO.
    `BR_COVER(pop_hsk_c, pop_valid[i] && pop_ready[i])

    // Exercise the deallocation path for every logical FIFO.
    `BR_COVER(dealloc_valid_c, dealloc_valid[i])
  end

  if (!HasStagingBuffer) begin : gen_no_staging_buffer_assumptions
    for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo
      // Without a staging buffer, pop_ready feeds the request path and must hold to avoid deadlock.
      `BR_ASSUME(pop_ready_hold_a, pop_ready[i] && !pop_valid[i] |=> pop_ready[i])
    end
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

    // Exercise every shared RAM read port.
    `BR_COVER(read_port_valid_c, data_ram_rd_addr_valid[p])
  end

  for (genvar i = 0; i < NumFifos; i++) begin : gen_head_to_read_checks
    logic head_has_read_addr;

    always_comb begin
      head_has_read_addr = 1'b0;
      for (int p = 0; p < NumReadPorts; p++) begin
        head_has_read_addr |= data_ram_rd_addr_valid[p] && (data_ram_rd_addr[p] == head[i]);
      end
    end

    // Every accepted head pointer must issue exactly as a shared RAM read request.
    `BR_ASSERT(accepted_head_has_read_a, head_hs[i] |-> head_has_read_addr)
  end

  // The number of accepted heads and read requests must match cycle-by-cycle.
  `BR_ASSERT(read_count_matches_head_hs_a, $countones(data_ram_rd_addr_valid) == $countones(head_hs
                                                                                               ))

  // The pop side can accept at most one head per physical read port per cycle.
  `BR_ASSERT(head_hs_read_port_capacity_a, $countones(head_hs) <= NumReadPorts)

  for (genvar p = 0; p < NumReadPorts; p++) begin : gen_ram_response_assumptions
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
  end

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

  // Returned RAM data for the selected FIFO must leave the pop interface in FIFO order.
  // The selected FIFO can receive RAM return data from any physical read port over time,
  // so the scoreboard has one incoming chunk per RAM read port and one outgoing chunk for
  // the selected FIFO's pop stream.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(NumReadPorts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPending)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_rsp_valid),
      .incoming_data(data_ram_rd_data),
      .outgoing_vld(pop_valid[fv_fifo_id] && pop_ready[fv_fifo_id]),
      .outgoing_data(pop_data[fv_fifo_id])
  );

  if (NumReadPorts < NumFifos) begin : gen_read_contention_cover
    // Exercise read-port contention when the configuration has fewer read ports than FIFOs.
    `BR_COVER(read_contention_c, $countones(head_valid) > NumReadPorts)
  end

  // Exercise a cycle where the controller uses all available read ports.
  `BR_COVER(all_read_ports_used_c, &data_ram_rd_addr_valid)

endmodule : br_fifo_shared_pop_ctrl_fpv_monitor

bind br_fifo_shared_pop_ctrl br_fifo_shared_pop_ctrl_fpv_monitor #(
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RegisterDeallocation(RegisterDeallocation),
    .RamReadLatency(RamReadLatency)
) monitor (.*);
