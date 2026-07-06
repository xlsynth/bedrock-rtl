// SPDX-License-Identifier: Apache-2.0

// SymbiYosys harness for the Bedrock-RTL round-robin arbiter.

module br_arb_rr_sby_harness #(
    parameter int NumRequesters = 2,
    localparam int WaitWidth = $clog2(NumRequesters + 1)
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request
);

  logic [NumRequesters-1:0] grant;

  br_arb_rr #(
      .NumRequesters(NumRequesters)
  ) dut (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .grant
  );

  logic [NumRequesters-1:0] priority_mask;
  logic [NumRequesters-1:0] last_grant;
  logic [NumRequesters-1:0] request_high;
  logic [NumRequesters-1:0] expected_grant;

  always_comb begin : calc_expected_grant
    logic found;
    priority_mask = dut.br_arb_rr_internal.gen_n_req.priority_mask;
    last_grant = dut.br_arb_rr_internal.gen_n_req.rr_state_internal.last_grant;
    request_high = request & ~priority_mask;
    expected_grant = '0;
    found = 1'b0;
    for (int i = 0; i < NumRequesters; i++) begin
      if (!found && request_high[i]) begin
        expected_grant[i] = 1'b1;
        found = 1'b1;
      end
    end
    for (int i = 0; i < NumRequesters; i++) begin
      if (!found && request[i]) begin
        expected_grant[i] = 1'b1;
        found = 1'b1;
      end
    end
  end

  logic fv_past_valid = 1'b0;
  logic fv_prev_rst;
  logic [NumRequesters-1:0] fv_prev_request;
  logic [NumRequesters-1:0] fv_prev_grant;
  logic [WaitWidth-1:0] fv_wait_count[NumRequesters];

  always @(posedge clk) begin
    fv_past_valid <= 1'b1;
    assume (rst == !fv_past_valid);

    if (fv_past_valid && !rst && !fv_prev_rst) begin
      for (int i = 0; i < NumRequesters; i++) begin
        if (fv_prev_request[i] && !fv_prev_grant[i]) begin
          assume (request[i]);
        end
      end
    end

    if (rst) begin
      for (int i = 0; i < NumRequesters; i++) begin
        fv_wait_count[i] <= '0;
      end
    end else begin
      assert ((grant & (grant - 1'b1)) == '0);
      assert (last_grant != '0 && ((last_grant & (last_grant - 1'b1)) == '0));
      assert ((grant & request) == grant);
      assert ((|request) == (|grant));
      assert (grant == expected_grant);

      for (int i = 0; i < NumRequesters; i++) begin
        if (!request[i] || grant[i] || !enable_priority_update) begin
          fv_wait_count[i] <= '0;
        end else begin
          assert (fv_wait_count[i] < NumRequesters);
          fv_wait_count[i] <= fv_wait_count[i] + 1'b1;
        end

        cover (last_grant[i]);
        cover (request[i] && priority_mask[i] && grant[i]);
      end

      cover (&request);
      cover (!enable_priority_update && |grant);
    end

    fv_prev_rst <= rst;
    fv_prev_request <= request;
    fv_prev_grant <= grant;
  end

endmodule : br_arb_rr_sby_harness
