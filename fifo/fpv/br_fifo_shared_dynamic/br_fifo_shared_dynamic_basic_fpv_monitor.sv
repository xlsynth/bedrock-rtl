// SPDX-License-Identifier: Apache-2.0


// br_fifo_shared_dynamic basic FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_basic_fpv_monitor #(
    parameter bit WolperColorEn = 0,
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit HasStagingBuffer = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Push side
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0] push_ready,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,

    // Pop side
    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data
);

  // ----------FV Modeling Code----------
  localparam int PortWidth = br_math::clamped_clog2(NumWritePorts);
  // pick a random FIFO to check
  logic [FifoIdWidth-1:0] fv_fifo_id;
  // pick a random write port for assertion
  logic [PortWidth-1:0] fv_wr_port;
  logic [NumWritePorts-1:0] fv_push_vr;

  `BR_ASSUME(fv_fifo_id_a, $stable(fv_fifo_id) && (fv_fifo_id < NumFifos))
  `BR_ASSUME(fv_wr_prt_a, $stable(fv_wr_port) && (fv_wr_port < NumWritePorts))

  // tracking valid push to fv_fifo_id
  always_comb begin
    fv_push_vr = 'd0;
    for (int n = 0; n < NumWritePorts; n++) begin
      fv_push_vr[n] = push_valid[n] && push_ready[n] && (push_fifo_id[n] == fv_fifo_id);
    end
  end

  // ----------FV assumptions----------
  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_asm
    `BR_ASSUME(push_fifo_id_legal_a, push_fifo_id[i] < NumFifos)
    if (EnableCoverPushBackpressure) begin : gen_back_pressure
      if (EnableAssertPushValidStability) begin : gen_push_valid_stable
        `BR_ASSUME(push_valid_stable_a, push_valid[i] && !push_ready[i] |=> push_valid[i])
      end
      if (EnableAssertPushDataStability) begin : gen_push_data_stable
        `BR_ASSUME(
            push_data_stable_a,
            push_valid[i] && !push_ready[i] |=> $stable(push_data[i]) && $stable(push_fifo_id[i]))
      end
    end else begin : gen_no_backpressure
      `BR_ASSUME(no_backpressure_a, push_valid[i] |-> push_ready[i])
    end
  end
  if (!HasStagingBuffer) begin : gen_no_staging_buffer
    for (genvar i = 0; i < NumFifos; i++) begin : gen_pop_ready_hold
      // pop_ready can't drop without its pop_valid
      `BR_ASSUME(pop_ready_hold_a, pop_ready[i] && !pop_valid[i] |=> pop_ready[i])
    end
  end

  // ----------FV assertions----------
  // RTL guarantees pop_valid && !pop_ready is not possible, so there is no check
  for (genvar i = 0; i < NumFifos; i++) begin : gen_ast
    `BR_ASSUME(pop_ready_liveness_a, s_eventually pop_ready[i])
  end
  `BR_ASSERT(no_deadlock_pop_a, fv_push_vr[fv_wr_port] |-> s_eventually pop_valid[fv_fifo_id])

  // ----------Data integrity Check----------
  // data pushed to same FIFO should be in order
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(NumWritePorts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(Depth + StagingBufferDepth)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_push_vr),
      .incoming_data(push_data),
      .outgoing_vld(pop_valid[fv_fifo_id] & pop_ready[fv_fifo_id]),
      .outgoing_data(pop_data[fv_fifo_id])
  );

endmodule : br_fifo_shared_dynamic_basic_fpv_monitor
