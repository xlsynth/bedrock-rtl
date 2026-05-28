// SPDX-License-Identifier: Apache-2.0

module br_arb_pri_rr_tb;
  timeunit 1ns; timeprecision 100ps;

  parameter int NumRequesters = 4;
  parameter int NumPriorities = 3;
  parameter int NumRandomCycles = 100;

  localparam int PriorityWidth = $clog2(NumPriorities);

  logic clk;
  logic rst;
  logic enable_priority_update;
  logic [NumRequesters-1:0] request;
  logic [NumRequesters-1:0][PriorityWidth-1:0] request_priority;
  logic [NumRequesters-1:0] grant;

  int rr_ptr;

  br_arb_pri_rr #(
      .NumRequesters(NumRequesters),
      .NumPriorities(NumPriorities)
  ) dut (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .request_priority,
      .grant
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [NumRequesters-1:0] expected_grant(
      input logic [NumRequesters-1:0] req,
      input logic [NumRequesters-1:0][PriorityWidth-1:0] pri
  );
    logic found_request;
    logic [PriorityWidth-1:0] max_priority;
    int idx;

    expected_grant = '0;
    found_request = 1'b0;
    max_priority = '0;

    for (int i = 0; i < NumRequesters; i++) begin
      if (req[i] && (!found_request || (pri[i] > max_priority))) begin
        found_request = 1'b1;
        max_priority = pri[i];
      end
    end

    if (found_request) begin
      for (int offset = 0; offset < NumRequesters; offset++) begin
        idx = (rr_ptr + offset) % NumRequesters;
        if (req[idx] && (pri[idx] == max_priority) && (expected_grant == '0)) begin
          expected_grant[idx] = 1'b1;
        end
      end
    end
  endfunction

  task automatic update_model(input logic [NumRequesters-1:0] grant_model);
    if (enable_priority_update && |request) begin
      for (int i = 0; i < NumRequesters; i++) begin
        if (grant_model[i]) begin
          rr_ptr = (i + 1) % NumRequesters;
        end
      end
    end
  endtask

  task automatic drive_and_check(
      input logic [NumRequesters-1:0] req,
      input logic [NumRequesters-1:0][PriorityWidth-1:0] pri,
      input logic enable_update,
      input string message
  );
    logic [NumRequesters-1:0] grant_expected;

    request = req;
    request_priority = pri;
    enable_priority_update = enable_update;
    #1;

    grant_expected = expected_grant(req, pri);
    td.check(grant === grant_expected,
             $sformatf("%s: got grant 0x%0h, expected 0x%0h",
                       message, grant, grant_expected));

    td.wait_cycles();
    update_model(grant_expected);
  endtask

  task automatic clear_priorities(output logic [NumRequesters-1:0][PriorityWidth-1:0] pri);
    for (int i = 0; i < NumRequesters; i++) begin
      pri[i] = '0;
    end
  endtask

  task automatic set_uniform_priority(
      output logic [NumRequesters-1:0][PriorityWidth-1:0] pri,
      input int priority_value
  );
    for (int i = 0; i < NumRequesters; i++) begin
      pri[i] = PriorityWidth'(priority_value);
    end
  endtask

  task automatic set_random_priorities(
      output logic [NumRequesters-1:0][PriorityWidth-1:0] pri
  );
    for (int i = 0; i < NumRequesters; i++) begin
      pri[i] = PriorityWidth'($urandom_range(0, NumPriorities - 1));
    end
  endtask

  task automatic reset_test;
    request = '0;
    request_priority = '0;
    enable_priority_update = 1'b0;
    rr_ptr = 0;
    td.reset_dut();
    td.wait_cycles();
  endtask

  initial begin
    logic [NumRequesters-1:0][PriorityWidth-1:0] pri;
    logic [NumRequesters-1:0] req;

    reset_test();
    clear_priorities(pri);
    drive_and_check('0, pri, 1'b1, "idle grants nothing");

    for (int i = 0; i < NumRequesters; i++) begin
      req = '0;
      req[i] = 1'b1;
      clear_priorities(pri);
      pri[i] = PriorityWidth'(NumPriorities - 1);
      drive_and_check(req, pri, 1'b1, $sformatf("single requester %0d", i));
    end

    reset_test();
    clear_priorities(pri);
    req = '0;
    req[0] = 1'b1;
    req[NumRequesters-1] = 1'b1;
    pri[0] = '0;
    pri[NumRequesters-1] = PriorityWidth'(NumPriorities - 1);
    drive_and_check(req, pri, 1'b1, "higher priority beats lower RR position");

    reset_test();
    req = '1;
    set_uniform_priority(pri, NumPriorities - 1);
    for (int i = 0; i < (2 * NumRequesters); i++) begin
      drive_and_check(req, pri, 1'b1, $sformatf("uniform priority rotation %0d", i));
    end

    reset_test();
    req = '1;
    set_uniform_priority(pri, NumPriorities - 1);
    for (int i = 0; i < NumRequesters; i++) begin
      drive_and_check(req, pri, 1'b0, $sformatf("priority update disabled %0d", i));
    end
    drive_and_check(req, pri, 1'b1, "priority update re-enabled");

    reset_test();
    for (int cycle = 0; cycle < NumRandomCycles; cycle++) begin
      req = NumRequesters'($urandom());
      set_random_priorities(pri);
      drive_and_check(req, pri, $urandom_range(0, 1), $sformatf("random cycle %0d", cycle));
    end

    request = '0;
    enable_priority_update = 1'b0;
    td.finish();
  end

endmodule : br_arb_pri_rr_tb
