// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pstatic_basic_fpv_monitor #(
    parameter int NumFifos = 2,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamReadLatency = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0][AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][AddrWidth-1:0] config_bound,
    input logic config_error,

    // Push side
    input logic                   push_valid,
    input logic                   push_ready,
    input logic [      Width-1:0] push_data,
    input logic [FifoIdWidth-1:0] push_fifo_id,
    input logic [   NumFifos-1:0] push_full,

    // Pop side
    input logic [NumFifos-1:0]            pop_valid,
    input logic [NumFifos-1:0]            pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0]            pop_empty
);
  localparam bit HasStagingBuffer = RegisterPopOutputs || RamReadLatency > 0;

  // ----------FV Modeling Code----------
  // pick a random FIFO to check
  logic [FifoIdWidth-1:0] fv_fifo_id;
  `BR_ASSUME(fv_fifo_id_a, $stable(fv_fifo_id) && (fv_fifo_id < NumFifos))
  // access to fv_fifo_id
  logic fv_push_valid;
  logic fv_pop_valid;
  // config error
  logic fv_config_error;

  assign fv_push_valid = push_valid & push_ready & (push_fifo_id == fv_fifo_id);
  assign fv_pop_valid  = pop_valid[fv_fifo_id] & pop_ready[fv_fifo_id];

  always_comb begin
    fv_config_error = 1'b0;
    for (int i = 0; i < NumFifos; i++) begin
      if (config_base[i] > config_bound[i]) begin
        fv_config_error = 1'b1;
      end
      if ((i < NumFifos - 1) && (config_base[i+1] <= config_bound[i])) begin
        fv_config_error = 1'b1;
      end
    end
  end

  // ----------FV assumptions----------
  `BR_ASSUME(push_fifo_id_legal_a, push_fifo_id < NumFifos)

  if (!EnableCoverPushBackpressure) begin : gen_no_push_backpressure
    `BR_ASSUME(no_push_backpressure_a, !(push_valid && !push_ready))
  end
  if (EnableAssertPushValidStability) begin : gen_push_valid_stable
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  end
  if (EnableAssertPushDataStability) begin : gen_push_data_stable
    `BR_ASSUME(push_data_stable_a,
               push_valid && !push_ready |=> $stable(push_data) && $stable(push_fifo_id))
  end
  if (!HasStagingBuffer) begin : gen_pop_ready_stable
    for (genvar i = 0; i < NumFifos; i++) begin : gen_pop_ready_stable_per_fifo
      `BR_ASSUME(pop_ready_stable_a, pop_ready[i] && !pop_valid[i] |=> pop_ready[i])
    end
  end

  for (genvar i = 0; i < NumFifos; i++) begin : gen_asm
    `BR_ASSUME(config_base_stable_a, $stable(config_base[i]))
    `BR_ASSUME(config_bound_stable_a, $stable(config_bound[i]))
    `BR_ASSUME(config_base_legal_a, config_base[i] < Depth)
    `BR_ASSUME(config_bound_legal_a, config_bound[i] < Depth)
    `BR_ASSUME(config_range_legal_a, config_bound[i] >= config_base[i])
    `BR_ASSUME(pop_ready_liveness_a, s_eventually pop_ready[i])
    if (i < NumFifos - 1) begin : gen_asc
      `BR_ASSUME(config_no_overlap_a, config_base[i+1] > config_bound[i])
    end
  end

  // ----------FV assertions----------
  if ((RegisterPopOutputs != 0) || (RamReadLatency != 0)) begin : gen_pop
    if (EnableAssertPushValidStability) begin : gen_pop_valid_stable
      `BR_ASSERT(pop_valid_stable_a,
                 pop_valid[fv_fifo_id] && !pop_ready[fv_fifo_id] |=> pop_valid[fv_fifo_id])
    end
    if (EnableAssertPushDataStability) begin : gen_pop_data_stable
      `BR_ASSERT(pop_data_stable_a,
                 pop_valid[fv_fifo_id] && !pop_ready[fv_fifo_id] |=> $stable(pop_data[fv_fifo_id]))
    end
  end

  `BR_ASSERT(push_config_error_a, config_error == fv_config_error)
  `BR_ASSERT(no_deadlock_pop_a, fv_push_valid |-> s_eventually pop_valid[fv_fifo_id])

  // ----------Data integrity Check----------
  // data pushed to same FIFO should be in order
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(Depth + StagingBufferDepth)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_push_valid),
      .incoming_data(push_data),
      .outgoing_vld(fv_pop_valid),
      .outgoing_data(pop_data[fv_fifo_id])
  );

endmodule
