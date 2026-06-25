// SPDX-License-Identifier: Apache-2.0

// Directed simulation testbench for br_arb_multi_rr.
//
// Scope:
// - Reset and idle grant behavior.
// - Directed single-requester, all-requester, and partial multi-grant scenarios.
// - Blocked priority-update behavior.
// - Grant, ordered-grant, and grant-count checks for every driven cycle.
// - Bazel-swept NumRequesters and MaxGrantPerCycle parameters.

module br_arb_multi_rr_tb;
  timeunit 1ns; timeprecision 100ps;

  parameter int NumRequesters = 5;
  parameter int MaxGrantPerCycle = 3;
  parameter int NumRandomCycles = 120;

  localparam int GrantCountWidth = $clog2(MaxGrantPerCycle + 1);
  localparam int NoGrantsAllowed = 0;
  localparam int OneGrantAllowed = 1;
  localparam logic PriorityUpdateDisabled = 1'b0;
  localparam logic PriorityUpdateEnabled = 1'b1;

  typedef logic [NumRequesters-1:0] requester_vec_t;
  typedef logic [MaxGrantPerCycle-1:0][NumRequesters-1:0] ordered_grant_t;

  logic clk;
  logic rst;
  logic enable_priority_update;
  requester_vec_t request;
  requester_vec_t grant;
  ordered_grant_t grant_ordered;
  logic [GrantCountWidth-1:0] grant_allowed;
  logic [GrantCountWidth-1:0] grant_count;

  int rr_ptr;

  br_arb_multi_rr #(
      .NumRequesters(NumRequesters),
      .MaxGrantPerCycle(MaxGrantPerCycle)
  ) dut (
      .clk,
      .rst,
      .enable_priority_update,
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

  // Build the ordered one-hot grants from the current modeled round-robin pointer.
  function automatic ordered_grant_t expected_grant_ordered(input requester_vec_t req,
                                                            input int allowed);
    int grant_idx;
    int requester_idx;

    expected_grant_ordered = '0;
    grant_idx = 0;

    for (int offset = 0; offset < NumRequesters; offset++) begin
      requester_idx = (rr_ptr + offset) % NumRequesters;
      if (req[requester_idx] && (grant_idx < allowed)) begin
        expected_grant_ordered[grant_idx][requester_idx] = 1'b1;
        grant_idx++;
      end
    end
  endfunction

  // Collapse the ordered grant slots into the DUT's combined grant vector view.
  function automatic requester_vec_t collapse_grants(input ordered_grant_t ordered);
    collapse_grants = '0;
    for (int i = 0; i < MaxGrantPerCycle; i++) begin
      collapse_grants |= ordered[i];
    end
  endfunction

  // Expected grant_count is the smaller of the active request count and allowance.
  function automatic logic [GrantCountWidth-1:0] expected_grant_count(input requester_vec_t req,
                                                                      input int allowed);
    int request_count;
    int expected_count;

    request_count = $countones(req);
    expected_count = (request_count < allowed) ? request_count : allowed;
    expected_grant_count = GrantCountWidth'(expected_count);
  endfunction

  // Advance the reference round-robin pointer to one past the last granted requester.
  task automatic update_model(input ordered_grant_t ordered_expected, input int allowed);
    int last_granted_idx;

    if (enable_priority_update && (request != '0) && (allowed > 0)) begin
      last_granted_idx = rr_ptr;
      for (int i = 0; i < MaxGrantPerCycle; i++) begin
        for (int requester_idx = 0; requester_idx < NumRequesters; requester_idx++) begin
          if (ordered_expected[i][requester_idx]) begin
            last_granted_idx = requester_idx;
          end
        end
      end
      rr_ptr = (last_granted_idx + 1) % NumRequesters;
    end
  endtask

  task automatic drive_inputs(input requester_vec_t req, input int allowed,
                              input logic enable_update);
    request = req;
    grant_allowed = GrantCountWidth'(allowed);
    enable_priority_update = enable_update;
    #1;
  endtask

  task automatic check_outputs(input requester_vec_t req, input int allowed,
                               input logic enable_update, output ordered_grant_t ordered_expected);
    requester_vec_t grant_expected;
    logic [GrantCountWidth-1:0] count_expected;

    ordered_expected = expected_grant_ordered(req, allowed);
    grant_expected   = collapse_grants(ordered_expected);
    count_expected   = expected_grant_count(req, allowed);

    td.check(grant === grant_expected, $sformatf(
             "grant mismatch for req 0x%0h allowed %0d update %0b: got 0x%0h, expected 0x%0h",
             req,
             allowed,
             enable_update,
             grant,
             grant_expected
             ));
    td.check(grant_ordered === ordered_expected, $sformatf(
             {
               "grant_ordered mismatch for req 0x%0h allowed %0d update %0b: ",
               "got 0x%0h, expected 0x%0h"
             },
             req,
             allowed,
             enable_update,
             grant_ordered,
             ordered_expected
             ));
    td.check(grant_count === count_expected, $sformatf(
             "grant_count mismatch for req 0x%0h allowed %0d update %0b: got %0d, expected %0d",
             req,
             allowed,
             enable_update,
             grant_count,
             count_expected
             ));
  endtask

  task automatic drive_and_check(input requester_vec_t req, input int allowed,
                                 input logic enable_update);
    ordered_grant_t ordered_expected;

    drive_inputs(req, allowed, enable_update);
    check_outputs(req, allowed, enable_update, ordered_expected);
    td.wait_cycles();
    update_model(ordered_expected, allowed);
  endtask

  task automatic reset_test;
    request = '0;
    grant_allowed = '0;
    enable_priority_update = 1'b0;
    rr_ptr = 0;
    td.reset_dut();
    td.wait_cycles();
  endtask

  task automatic randomize_sparse_request(output requester_vec_t req_out);
    int set_count;

    req_out = '0;
    for (int i = 0; i < NumRequesters; i++) begin
      req_out[i] = $urandom_range(0, 1);
    end

    set_count = $countones(req_out);
    // Keep this phase sparse: all-zero is an idle case and all-one is covered by full rotation.
    if (set_count == 0) begin
      req_out[$urandom_range(0, NumRequesters-1)] = 1'b1;
    end else if (set_count == NumRequesters) begin
      req_out[$urandom_range(0, NumRequesters-1)] = 1'b0;
    end
  endtask

  initial begin
    requester_vec_t req;
    int allowed;

    reset_test();
    // Confirm idle cycles never produce grants, independent of grant_allowed.
    drive_and_check('0, NoGrantsAllowed, PriorityUpdateEnabled);
    drive_and_check('0, MaxGrantPerCycle, PriorityUpdateEnabled);

    // Walk each requester through a one-hot request to check direct grant mapping.
    for (int i = 0; i < NumRequesters; i++) begin
      req = '0;
      req[i] = 1'b1;
      drive_and_check(req, MaxGrantPerCycle, PriorityUpdateEnabled);
    end

    reset_test();
    // Hold all requests while grant_allowed is zero, then verify priority did not advance.
    req = '1;
    drive_and_check(req, NoGrantsAllowed, PriorityUpdateEnabled);
    drive_and_check(req, NoGrantsAllowed, PriorityUpdateEnabled);
    drive_and_check(req, OneGrantAllowed, PriorityUpdateEnabled);

    reset_test();
    // Exercise multi-grant round-robin ordering across more than one full rotation.
    req = '1;
    for (int i = 0; i < (2 * NumRequesters); i++) begin
      drive_and_check(req, MaxGrantPerCycle, PriorityUpdateEnabled);
    end

    reset_test();
    // Random sparse request vectors check partial grant lists without assuming fixed indices.
    for (int i = 0; i < NumRequesters; i++) begin
      randomize_sparse_request(req);
      // Cycle through 1..MaxGrantPerCycle; zero-grant behavior is covered above.
      allowed = 1 + (i % MaxGrantPerCycle);
      drive_and_check(req, allowed, PriorityUpdateEnabled);
    end

    reset_test();
    // Keep requests stable while priority updates are blocked, then re-enable rotation.
    req = '1;
    for (int i = 0; i < NumRequesters; i++) begin
      drive_and_check(req, MaxGrantPerCycle, PriorityUpdateDisabled);
    end
    drive_and_check(req, MaxGrantPerCycle, PriorityUpdateEnabled);

    reset_test();
    // Bounded random request, grant allowance, and update-enable combinations.
    for (int cycle = 0; cycle < NumRandomCycles; cycle++) begin
      req = NumRequesters'($urandom());
      allowed = $urandom_range(0, MaxGrantPerCycle);
      drive_and_check(req, allowed, $urandom_range(0, 1));
    end

    request = '0;
    grant_allowed = '0;
    enable_priority_update = 1'b0;
    td.finish();
  end

endmodule : br_arb_multi_rr_tb
