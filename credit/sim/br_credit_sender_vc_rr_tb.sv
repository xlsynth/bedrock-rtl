// Copyright 2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL VC-based Credit Sender Testbench
module br_credit_sender_vc_rr_tb;
  //------------------------------------------
  // Parameters
  //------------------------------------------
  parameter int NumVcs = 2;
  parameter int Width = 8;
  parameter int MaxCredit = 4;
  parameter int PopCreditMaxChange = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter int PushItemsPerVc = 100;
  localparam int TotalPushItems = NumVcs * 100;

  localparam int VcWidth = $clog2(NumVcs);
  localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1);
  localparam int CountWidth = $clog2(MaxCredit + 1);

  logic                                   clk;
  logic                                   rst;
  logic [ NumVcs-1:0]                     push_ready;
  logic [ NumVcs-1:0]                     push_valid;
  logic [ NumVcs-1:0][         Width-1:0] push_data;

  logic [ NumVcs-1:0]                     request;
  logic [ NumVcs-1:0]                     can_grant;
  logic [ NumVcs-1:0]                     grant;
  logic                                   enable_priority_update;

  logic                                   pop_sender_in_reset;
  logic                                   pop_receiver_in_reset;
  logic [ NumVcs-1:0][PopCreditWidth-1:0] pop_credit;
  logic                                   pop_valid;
  logic [  Width-1:0]                     pop_data;
  logic [VcWidth-1:0]                     pop_vc;

  logic [  Width-1:0]                     data_sb                [NumVcs][$];

  br_credit_sender_vc #(
      .NumVcs(NumVcs),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .PopCreditMaxChange(PopCreditMaxChange),
      .RegisterPopOutputs(RegisterPopOutputs)
  ) dut (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_sender_in_reset,
      .pop_receiver_in_reset,
      .pop_credit,
      .pop_valid,
      .pop_data,
      .pop_vc,
      .credit_initial('0),
      .credit_withhold('0),
      .credit_count(),
      .credit_available()
  );

  br_arb_rr_internal #(
      .NumRequesters(NumVcs)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update
  );

  br_test_driver td (
      .clk,
      .rst
  );

  int recv_credit[NumVcs];

  task automatic return_credits();
    int total_received;

    for (int i = 0; i < NumVcs; i++) begin
      recv_credit[i] = MaxCredit;
      pop_credit[i]  = '0;
    end
    pop_receiver_in_reset = 0;
    total_received = 0;

    @(negedge clk);

    while (total_received < TotalPushItems) begin
      // Return credit if we have any
      for (int i = 0; i < NumVcs; i++) begin
        int max_credit_to_return = br_math::min2(recv_credit[i], PopCreditMaxChange);
        int credit_to_return;
        if (recv_credit[i] > 0) begin
          $display("VC %d has %d credits to return", i, recv_credit[i]);
          credit_to_return = $urandom_range(0, max_credit_to_return);
          recv_credit[i] -= credit_to_return;
          pop_credit[i] = credit_to_return;
          $display("Returning %d credits for VC %d", credit_to_return, i);
        end else begin
          pop_credit[i] = 0;
        end
      end
      @(posedge clk);
      // Check the pop_valid to see if we are getting credits from sender
      for (int i = 0; i < NumVcs; i++) begin
        if (pop_valid && pop_vc == i) begin
          $display("Received data for VC %d", i);
          recv_credit[i] += 1;
          total_received++;
        end
      end
      @(negedge clk);
    end
    pop_credit = 0;
    $display("Received all %d items", total_received);
  endtask

  task automatic wait_for_push_ready(int vc);
    int timeout = 1000;
    while (!push_ready[vc] && timeout > 0) begin
      timeout--;
      @(posedge clk);
    end
    td.check(timeout > 0, $sformatf("Timed out waiting for push ready %d", vc));
  endtask

  task automatic push_items(int vc);
    push_valid[vc] = 0;
    push_data[vc]  = 0;

    @(negedge clk);

    for (int i = 0; i < PushItemsPerVc; i++) begin
      int data = $urandom_range(0, 2 ** Width - 1);

      data_sb[vc].push_back(data);

      push_data[vc]  = data;
      push_valid[vc] = 1;
      @(posedge clk);
      wait_for_push_ready(vc);
      @(negedge clk);
    end
    push_valid[vc] = 0;
    push_data[vc]  = 0;
  endtask

  task automatic check_pop_items();
    int total_received = 0;

    @(posedge clk);

    while (total_received < TotalPushItems) begin
      if (pop_valid) begin
        logic [Width-1:0] expected_data = data_sb[pop_vc].pop_front();
        td.check_integer(expected_data, pop_data);
        total_received++;
      end
      @(posedge clk);
    end
  endtask

  task automatic drain_credits();
    int any_left;

    $display("Draining remaining credits back to sender");
    pop_credit = 0;

    do begin
      any_left = 0;

      @(negedge clk);
      for (int i = 0; i < NumVcs; i++) begin
        int credit_to_return = br_math::min2(recv_credit[i], PopCreditMaxChange);
        pop_credit[i] = credit_to_return;
        recv_credit[i] -= credit_to_return;
        if (recv_credit[i] > 0) any_left = 1;
      end

      @(posedge clk);

      // De-assert after one cycle
      @(negedge clk);
      pop_credit = 0;
    end while (any_left);
  endtask

  initial begin
    push_valid = 0;
    push_data = 0;
    pop_credit = 0;
    pop_receiver_in_reset = 0;

    td.reset_dut();

    fork
      return_credits();
      check_pop_items();
    join_none

    for (int i = 0; i < NumVcs; i++) begin
      automatic int vc = i;
      fork
        push_items(vc);
      join_none
    end

    wait fork;

    // Ensure all outstanding credits are returned to the sender
    drain_credits();

    td.finish();
  end

endmodule
