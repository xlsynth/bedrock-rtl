`timescale 1ns / 1ps

module br_arb_multi_fixed_tb;

  // Parameters
  parameter int NumRequesters = 5;
  parameter int MaxGrantPerCycle = 3;

  localparam int NumRequestCombos = 2 ** NumRequesters;
  localparam int GrantCountWidth = $clog2(MaxGrantPerCycle + 1);


  logic clk;
  logic rst;

  logic [NumRequesters-1:0] request;
  logic [NumRequesters-1:0] grant;
  logic [MaxGrantPerCycle-1:0][NumRequesters-1:0] grant_ordered;
  logic [GrantCountWidth-1:0] grant_allowed;
  logic [GrantCountWidth-1:0] grant_count;

  br_arb_multi_fixed #(
      .NumRequesters(NumRequesters),
      .MaxGrantPerCycle(MaxGrantPerCycle)
  ) dut (
      .clk,
      .rst,
      .request,
      .grant,
      .grant_ordered,
      .grant_allowed,
      .grant_count
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_grant(int request, int num_grants);
    int expected_count;
    int expected_grant;
    int cur_count;

    expected_count = br_math::min2($countones(request), num_grants);
    expected_grant = 0;
    cur_count = 0;

    td.check_integer(grant_count, expected_count, "Grant count mismatch");

    for (int i = 0; i < NumRequesters; i++) begin
      if (cur_count >= expected_count) begin
        break;
      end

      if (request[i]) begin
        td.check_integer(grant_ordered[cur_count], 1 << i, $sformatf("grant_ordered[%d] mismatch", i
                         ));
        expected_grant |= (1 << i);
        cur_count++;
      end
    end

    td.check_integer(grant, expected_grant, "Grant mismatch");
  endtask

  initial begin
    request = '0;
    grant_allowed = '0;
    td.reset_dut();

    for (int num_grants = 1; num_grants < MaxGrantPerCycle; num_grants++) begin
      for (int request_vec = 0; request_vec < NumRequestCombos; request_vec++) begin
        @(negedge clk);
        grant_allowed = num_grants;
        request = request_vec;
        @(posedge clk);
        check_grant(request_vec, num_grants);
      end
    end

    td.finish();
  end

endmodule
