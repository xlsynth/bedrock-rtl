// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Weighted Round-Robin Flow Mux Testbench

module br_flow_mux_weighted_rr_tb;
  parameter int NumFlows = 4;
  parameter int Width = 8;
  parameter int MaxWeight = 4;
  parameter int MaxAccumulatedWeight = 8;
  parameter int NumRandomCycles = 32;
  parameter bit UsePairwiseArb = 0;

  localparam int WeightWidth = $clog2(MaxWeight + 1);

  logic clk;
  logic rst;
  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic [NumFlows-1:0][WeightWidth-1:0] cfg_weight;
  logic pop_ready;
  logic pop_valid_unstable;
  logic [Width-1:0] pop_data_unstable;

  int rr_ptr;
  int unsigned accumulated_weight[NumFlows];

  br_flow_mux_weighted_rr #(
      .NumFlows(NumFlows),
      .Width(Width),
      .MaxWeight(MaxWeight),
      .MaxAccumulatedWeight(MaxAccumulatedWeight),
      .UsePairwiseArb(UsePairwiseArb),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .cfg_weight,
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [NumFlows-1:0] expected_grant(input logic [NumFlows-1:0] req);
    logic [NumFlows-1:0] high_priority_request;
    logic [NumFlows-1:0] eligible_request;
    int idx;

    expected_grant = '0;
    if (NumFlows == 1) begin
      expected_grant = req;
    end else begin
      high_priority_request = '0;
      for (int i = 0; i < NumFlows; i++) begin
        high_priority_request[i] = req[i] && (accumulated_weight[i] != 0);
      end

      eligible_request = |high_priority_request ? high_priority_request : req;
      for (int offset = 0; offset < NumFlows; offset++) begin
        idx = (rr_ptr + offset) % NumFlows;
        if (eligible_request[idx] && (expected_grant == '0)) begin
          expected_grant[idx] = 1'b1;
        end
      end
    end
  endfunction

  function automatic logic [Width-1:0] expected_data(input logic [NumFlows-1:0] grant);
    expected_data = '0;
    for (int i = 0; i < NumFlows; i++) begin
      if (grant[i]) begin
        expected_data = push_data[i];
      end
    end
  endfunction

  task automatic update_model(input logic [NumFlows-1:0] grant);
    logic any_high_priority_request;
    int unsigned next_weight;

    if (pop_ready && |push_valid) begin
      any_high_priority_request = 1'b0;
      for (int i = 0; i < NumFlows; i++) begin
        any_high_priority_request |= push_valid[i] && (accumulated_weight[i] != 0);
      end

      for (int i = 0; i < NumFlows; i++) begin
        next_weight = accumulated_weight[i];
        if (!any_high_priority_request) begin
          next_weight += cfg_weight[i];
          if (next_weight > MaxAccumulatedWeight) begin
            next_weight = MaxAccumulatedWeight;
          end
        end
        if (grant[i] && (next_weight != 0)) begin
          next_weight--;
        end
        accumulated_weight[i] = next_weight;
      end

      if (NumFlows > 1) begin
        for (int i = 0; i < NumFlows; i++) begin
          if (grant[i]) begin
            rr_ptr = (i + 1) % NumFlows;
          end
        end
      end
    end
  endtask

  task automatic check_cycle(input string message);
    logic [NumFlows-1:0] grant_expected;
    logic [NumFlows-1:0] accepted_expected;

    grant_expected = expected_grant(push_valid);
    accepted_expected = pop_ready ? grant_expected : '0;
    td.check((push_ready & push_valid) === accepted_expected, $sformatf("%s: accepted flow", message
             ));
    td.check(pop_valid_unstable === |push_valid, $sformatf("%s: pop_valid", message));
    if (|push_valid) begin
      td.check(pop_data_unstable === expected_data(grant_expected), $sformatf(
               "%s: pop_data", message));
    end
  endtask

  task automatic step_and_check(input string message);
    logic [NumFlows-1:0] grant_expected;

    check_cycle(message);
    grant_expected = expected_grant(push_valid);
    @(posedge clk);
    update_model(grant_expected);
    @(negedge clk);
  endtask

  task automatic drive_and_check(input logic [NumFlows-1:0] valid,
                                 input logic [NumFlows-1:0][WeightWidth-1:0] weight,
                                 input logic ready, input string message);
    push_valid = valid;
    cfg_weight = weight;
    pop_ready  = ready;
    #1;
    step_and_check(message);
  endtask

  task automatic set_uniform_weight(output logic [NumFlows-1:0][WeightWidth-1:0] weight,
                                    input int value);
    for (int i = 0; i < NumFlows; i++) begin
      weight[i] = WeightWidth'(value);
    end
  endtask

  task automatic set_indexed_weight(output logic [NumFlows-1:0][WeightWidth-1:0] weight);
    for (int i = 0; i < NumFlows; i++) begin
      weight[i] = WeightWidth'(1 + (i % MaxWeight));
    end
  endtask

  task automatic set_random_weight(output logic [NumFlows-1:0][WeightWidth-1:0] weight);
    for (int i = 0; i < NumFlows; i++) begin
      weight[i] = WeightWidth'($urandom_range(1, MaxWeight));
    end
  endtask

  task automatic reset_test;
    push_valid = '0;
    pop_ready = 1'b0;
    rr_ptr = 0;
    for (int i = 0; i < NumFlows; i++) begin
      accumulated_weight[i] = 0;
      push_data[i] = Width'(8'h10 + (i * 8'h11));
      cfg_weight[i] = WeightWidth'(1);
    end
    td.reset_dut();
  endtask

  initial begin
    logic [NumFlows-1:0][WeightWidth-1:0] weight;
    logic [NumFlows-1:0] valid;

    reset_test();
    set_uniform_weight(weight, 1);
    drive_and_check('0, weight, 1'b1, "idle mux should be invalid");

    valid = '1;
    for (int i = 0; i < (2 * NumFlows); i++) begin
      drive_and_check(valid, weight, 1'b1, $sformatf("equal weights rotation %0d", i));
    end

    reset_test();
    set_indexed_weight(weight);
    for (int i = 0; i < (4 * NumFlows); i++) begin
      drive_and_check(valid, weight, 1'b1, $sformatf("indexed weights cycle %0d", i));
    end

    drive_and_check(valid, weight, 1'b0, "backpressure suppresses acceptance");
    drive_and_check(valid, weight, 1'b0, "backpressure holds weighted RR priority");
    drive_and_check(valid, weight, 1'b1, "weighted RR priority resumes after backpressure");

    reset_test();
    for (int cycle = 0; cycle < NumRandomCycles; cycle++) begin
      valid = NumFlows'($urandom());
      set_random_weight(weight);
      drive_and_check(valid, weight, $urandom_range(0, 1), $sformatf("random cycle %0d", cycle));
    end

    push_valid = '0;
    pop_ready  = 1'b0;
    td.finish();
  end

endmodule : br_flow_mux_weighted_rr_tb
