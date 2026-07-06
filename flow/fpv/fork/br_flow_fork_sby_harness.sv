// SPDX-License-Identifier: Apache-2.0

// SymbiYosys harness for the Bedrock-RTL flow fork.

module br_flow_fork_sby_harness #(
    parameter int NumFlows = 1,
    parameter bit EnableCoverPushBackpressure = 1
) (
    input logic clk,
    input logic rst,
    input logic push_valid,
    input logic [NumFlows-1:0] pop_ready
);

  logic push_ready;
  logic [NumFlows-1:0] pop_valid_unstable;

  br_flow_fork #(
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertFinalNotValid(0)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid_unstable
  );

  logic fv_past_valid = 1'b0;
  logic fv_prev_rst;
  logic fv_prev_push_ready;
  logic fv_prev_push_valid;

  always @(posedge clk) begin
    fv_past_valid <= 1'b1;
    assume (rst == !fv_past_valid);

    if (fv_past_valid && !rst && !fv_prev_rst) begin
      if (EnableCoverPushBackpressure && fv_prev_push_valid && !fv_prev_push_ready) begin
        assume (push_valid);
      end
    end

    if (!rst) begin
      if (!EnableCoverPushBackpressure && !push_ready) begin
        assume (!push_valid);
      end

      assert (push_ready == &pop_ready);
      for (int i = 0; i < NumFlows; i++) begin
        assert (pop_valid_unstable[i] == (push_valid && &(pop_ready | (NumFlows'(1) << i))));
      end
      if (push_valid && push_ready) begin
        assert (&pop_valid_unstable);
      end

      cover (push_valid && push_ready);
      if (EnableCoverPushBackpressure) begin
        cover (push_valid && !push_ready);
      end
    end

    fv_prev_rst <= rst;
    fv_prev_push_ready <= push_ready;
    fv_prev_push_valid <= push_valid;
  end

endmodule : br_flow_fork_sby_harness
