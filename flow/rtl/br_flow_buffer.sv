// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Buffer
//
// A configurable dataflow buffer with depth ranging from 0 to N entries.
// Uses the AMBA-inspired ready-valid handshake protocol for synchronizing
// pipeline stages and stalling when encountering backpressure hazards.
//
// This module is a convenience wrapper that instantiates various combinations
// of flow regs for shallow depths or a flop-based FIFO for deeper storage.
//
// Depth | RegisterPushOutputs | RegisterPopOutputs | Implementation
// ------|---------------------|--------------------|-------------------------------
// 0     | N/A                 | N/A                | Combinational pass-through
// 1     | 0                   | 0                  | br_flow_reg_none
// 1     | 0                   | 1                  | br_flow_reg_fwd
// 1     | 1                   | 0                  | br_flow_reg_rev
// 1     | 1                   | 1                  | Unsupported
// 2     | 0                   | 0                  | br_flow_reg_none + br_flow_reg_none
// 2     | 0                   | 1                  | br_flow_reg_none + br_flow_reg_fwd
// 2     | 1                   | 0                  | br_flow_reg_rev + br_flow_reg_none
// 2     | 1                   | 1                  | br_flow_reg_both
// 3+    | 0                   | 0                  | Unsupported
// 3+    | 0                   | 1                  | Unsupported
// 3+    | 1                   | 0                  | br_fifo_flops with bypass
// 3+    | 1                   | 1                  | br_fifo_flops with bypass and pop outputs registered

`include "br_asserts.svh"
`include "br_unused.svh"

module br_flow_buffer #(
    // Must be at least 0
    parameter int Depth = 1,
    // Must be at least 1
    parameter int Width = 1,
    // If 1, then push_ready comes directly from a register.
    parameter bit RegisterPushOutputs = (Depth > 1),
    // If 1, then pop_valid and pop_data come directly from registers.
    parameter bit RegisterPopOutputs = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input logic clk,
    input logic rst,  // Synchronous active-high reset.

    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  if (Depth == 0) begin : gen_no_reg
    assign push_ready = pop_ready;
    assign pop_valid  = push_valid;
    assign pop_data   = push_data;

    `BR_UNUSED(clk)
    `BR_UNUSED(rst)

  end else if (Depth == 1 && !RegisterPushOutputs && !RegisterPopOutputs) begin : gen_flow_reg_none
    br_flow_reg_none #(
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
    ) br_flow_reg_none (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );

  end else if (Depth == 1 && !RegisterPushOutputs && RegisterPopOutputs) begin : gen_flow_reg_fwd
    br_flow_reg_fwd #(
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );

  end else if (Depth == 1 && RegisterPushOutputs && !RegisterPopOutputs) begin : gen_flow_reg_rev
    br_flow_reg_rev #(
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
    ) br_flow_reg_rev (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );

  end else if (Depth == 2 && RegisterPushOutputs && RegisterPopOutputs) begin : gen_flow_reg_both
    br_flow_reg_both #(
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
    ) br_flow_reg_both (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data
    );

  end else if (Depth == 2) begin : gen_depth_2
    logic             stage1_ready;
    logic             stage1_valid;
    logic [Width-1:0] stage1_data;

    if (RegisterPushOutputs) begin : gen_stage1_rev
      br_flow_reg_rev #(
          .Width(Width),
          .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
          .EnableAssertPushValidStability(EnableAssertPushValidStability),
          .EnableAssertPushDataStability(EnableAssertPushDataStability),
          .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
          .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
      ) br_flow_reg_rev (
          .clk,
          .rst,
          .push_ready,
          .push_valid,
          .push_data,
          .pop_ready(stage1_ready),
          .pop_valid(stage1_valid),
          .pop_data (stage1_data)
      );
    end else begin : gen_stage1_none
      br_flow_reg_none #(
          .Width(Width),
          .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
          .EnableAssertPushValidStability(EnableAssertPushValidStability),
          .EnableAssertPushDataStability(EnableAssertPushDataStability),
          .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
          .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
      ) br_flow_reg_none (
          .clk,
          .rst,
          .push_ready,
          .push_valid,
          .push_data,
          .pop_ready(stage1_ready),
          .pop_valid(stage1_valid),
          .pop_data (stage1_data)
      );
    end

    if (RegisterPopOutputs) begin : gen_stage2_fwd
      br_flow_reg_fwd #(
          .Width(Width),
          Stage 2 can still
          // Stage 2 can experience internal backpressure without backpressuring the input
          .EnableCoverPushBackpressure(1),
          // Stage 1 always provides stable inputs to stage 2
          .EnableAssertPushValidStability(1),
          .EnableAssertPushDataStability(1),
          .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_flow_reg_fwd (
          .clk,
          .rst,
          .push_ready(stage1_ready),
          .push_valid(stage1_valid),
          .push_data (stage1_data),
          .pop_ready,
          .pop_valid,
          .pop_data
      );
    end else begin : gen_stage2_none
      br_flow_reg_none #(
          .Width(Width),
          // Stage 2 can experience internal backpressure without backpressuring the input
          .EnableCoverPushBackpressure(1),
          // Stage 1 always provides stable inputs to stage 2
          .EnableAssertPushValidStability(1),
          .EnableAssertPushDataStability(1),
          .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_flow_reg_none (
          .clk,
          .rst,
          .push_ready(stage1_ready),
          .push_valid(stage1_valid),
          .push_data (stage1_data),
          .pop_ready,
          .pop_valid,
          .pop_data
      );
    end

  end else if (Depth >= 3 && RegisterPushOutputs) begin : gen_fifo
    // Uses a bypass FIFO with an optional 'flow_reg_fwd' on the pop side.
    // The FIFO drives push_ready from a full register and does not currently
    // support a combinational path from pop_ready to push_ready.
    br_fifo_flops #(
        .Depth(Depth),
        .Width(Width),
        .EnableBypass(1),
        .RegisterPopOutputs(RegisterPopOutputs),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertPushDataStability(EnableAssertPushDataStability),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
    ) br_fifo_flops (
        .clk,
        .rst,
        .push_ready,
        .push_valid,
        .push_data,
        .pop_ready,
        .pop_valid,
        .pop_data,
        .full      (),
        .full_next (),
        .slots     (),
        .slots_next(),
        .empty     (),
        .empty_next(),
        .items     (),
        .items_next()
    );

  end else begin : gen_unsupported
    `BR_ASSERT_STATIC(unsupported_parameter_combination_a, 0)
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_buffer
