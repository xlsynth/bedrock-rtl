// SPDX-License-Identifier: Apache-2.0

module br_arb_weighted_lru_tb;
  timeunit 1ns; timeprecision 100ps;

  parameter int NumRequesters = 4;
  parameter int MaxWeight = 4;
  parameter int MaxAccumulatedWeight = 8;
  parameter int NumRandomCycles = 120;

  localparam int WeightWidth = $clog2(MaxWeight + 1);

  logic clk;
  logic rst;
  logic enable_priority_update;
  logic [NumRequesters-1:0] request;
  logic [NumRequesters-1:0][WeightWidth-1:0] request_weight;
  logic [NumRequesters-1:0] grant;

  int unsigned accumulated_weight[NumRequesters];
  int unsigned lru_priority[NumRequesters];

  br_arb_weighted_lru #(
      .NumRequesters(NumRequesters),
      .MaxWeight(MaxWeight),
      .MaxAccumulatedWeight(MaxAccumulatedWeight)
  ) dut (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .request_weight,
      .grant
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [NumRequesters-1:0] expected_grant(input logic [NumRequesters-1:0] req);
    logic [NumRequesters-1:0] high_priority_request;
    logic [NumRequesters-1:0] eligible_request;
    int unsigned highest_lru_priority;

    expected_grant = '0;

    if (NumRequesters == 1) begin
      expected_grant = req;
    end else begin
      high_priority_request = '0;
      for (int i = 0; i < NumRequesters; i++) begin
        high_priority_request[i] = req[i] && (accumulated_weight[i] != 0);
      end

      eligible_request = |high_priority_request ? high_priority_request : req;
      highest_lru_priority = 0;
      for (int i = 0; i < NumRequesters; i++) begin
        if (eligible_request[i] &&
            ((expected_grant == '0) || (lru_priority[i] > highest_lru_priority))) begin
          expected_grant = NumRequesters'(1) << i;
          highest_lru_priority = lru_priority[i];
        end
      end
    end
  endfunction

  task automatic update_model(input logic [NumRequesters-1:0] grant_model);
    logic any_high_priority_request;
    int unsigned granted_lru_priority;
    int unsigned next_weight;

    if (enable_priority_update && |request) begin
      any_high_priority_request = 1'b0;
      for (int i = 0; i < NumRequesters; i++) begin
        any_high_priority_request |= request[i] && (accumulated_weight[i] != 0);
      end

      for (int i = 0; i < NumRequesters; i++) begin
        next_weight = accumulated_weight[i];
        if (!any_high_priority_request) begin
          next_weight += request_weight[i];
          if (next_weight > MaxAccumulatedWeight) begin
            next_weight = MaxAccumulatedWeight;
          end
        end
        if (grant_model[i] && (next_weight != 0)) begin
          next_weight--;
        end
        accumulated_weight[i] = next_weight;
      end

      if (NumRequesters > 1) begin
        granted_lru_priority = 0;
        for (int i = 0; i < NumRequesters; i++) begin
          if (grant_model[i]) begin
            granted_lru_priority = lru_priority[i];
          end
        end
        for (int i = 0; i < NumRequesters; i++) begin
          if (grant_model[i]) begin
            lru_priority[i] = 0;
          end else if (lru_priority[i] < granted_lru_priority) begin
            lru_priority[i]++;
          end
        end
      end
    end
  endtask

  task automatic drive_and_check(input logic [NumRequesters-1:0] req,
                                 input logic [NumRequesters-1:0][WeightWidth-1:0] weight,
                                 input logic enable_update, input string message);
    logic [NumRequesters-1:0] grant_expected;

    request = req;
    request_weight = weight;
    enable_priority_update = enable_update;
    #1;

    grant_expected = expected_grant(req);
    td.check(grant === grant_expected, $sformatf(
             "%s: got grant 0x%0h, expected 0x%0h", message, grant, grant_expected));

    td.wait_cycles();
    update_model(grant_expected);
  endtask

  task automatic set_uniform_weight(output logic [NumRequesters-1:0][WeightWidth-1:0] weight,
                                    input int value);
    for (int i = 0; i < NumRequesters; i++) begin
      weight[i] = WeightWidth'(value);
    end
  endtask

  task automatic set_indexed_weight(output logic [NumRequesters-1:0][WeightWidth-1:0] weight);
    for (int i = 0; i < NumRequesters; i++) begin
      weight[i] = WeightWidth'(1 + (i % MaxWeight));
    end
  endtask

  task automatic set_random_weight(output logic [NumRequesters-1:0][WeightWidth-1:0] weight);
    for (int i = 0; i < NumRequesters; i++) begin
      weight[i] = WeightWidth'($urandom_range(1, MaxWeight));
    end
  endtask

  task automatic reset_test;
    request = '0;
    request_weight = '0;
    enable_priority_update = 1'b0;
    for (int i = 0; i < NumRequesters; i++) begin
      accumulated_weight[i] = 0;
      lru_priority[i] = NumRequesters;
      request_weight[i] = WeightWidth'(1);
    end
    td.reset_dut();
    td.wait_cycles();
  endtask

  initial begin
    logic [NumRequesters-1:0][WeightWidth-1:0] weight;
    logic [NumRequesters-1:0] req;

    reset_test();
    set_uniform_weight(weight, 1);
    drive_and_check('0, weight, 1'b1, "idle grants nothing");

    req = '1;
    if (NumRequesters == 1) begin
      drive_and_check(req, weight, 1'b1, "single requester grant");
    end else begin
      for (int i = 0; i < (2 * NumRequesters); i++) begin
        drive_and_check(req, weight, 1'b1, $sformatf("equal weights LRU cycle %0d", i));
      end

      reset_test();
      req = '1;
      set_indexed_weight(weight);
      for (int i = 0; i < (4 * NumRequesters); i++) begin
        drive_and_check(req, weight, 1'b1, $sformatf("indexed weights cycle %0d", i));
      end

      for (int i = 0; i < NumRequesters; i++) begin
        drive_and_check(req, weight, 1'b0, $sformatf("priority update disabled %0d", i));
      end
      drive_and_check(req, weight, 1'b1, "priority update re-enabled");
    end

    reset_test();
    for (int cycle = 0; cycle < NumRandomCycles; cycle++) begin
      req = NumRequesters'($urandom());
      set_random_weight(weight);
      drive_and_check(req, weight, $urandom_range(0, 1), $sformatf("random cycle %0d", cycle));
    end

    request = '0;
    enable_priority_update = 1'b0;
    td.finish();
  end

endmodule : br_arb_weighted_lru_tb
