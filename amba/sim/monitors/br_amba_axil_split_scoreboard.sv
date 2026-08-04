// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axil_sim_pkg::*;
import br_amba_axil_monitor_sim_pkg::*;
import br_amba_axil_split_sim_pkg::*;
import br_amba_sim_pkg::*;

`include "br_amba_sim_macros.svh"

// br_amba_axil_split scoreboard.
//
// The scoreboard owns split-specific prediction and checking. Generic AXI-Lite
// monitors provide observed root/trunk/branch channel queues with timestamps.
module br_amba_axil_split_scoreboard #(
    parameter int NumBranchAddrRanges = 1,
    parameter bit NormalizeBranchAddress = 0
) (
    output logic failed
);

  axil_aw_observation_t root_aw_q[$];
  axil_w_observation_t root_w_q[$];
  axil_ar_observation_t root_ar_q[$];
  axil_b_observation_t root_b_q[$];
  axil_r_observation_t root_r_q[$];
  axil_aw_observation_t trunk_aw_q[$];
  axil_w_observation_t trunk_w_q[$];
  axil_ar_observation_t trunk_ar_q[$];
  axil_b_observation_t trunk_b_q[$];
  axil_r_observation_t trunk_r_q[$];
  axil_aw_observation_t branch_aw_q[$];
  axil_w_observation_t branch_w_q[$];
  axil_ar_observation_t branch_ar_q[$];
  axil_b_observation_t branch_b_q[$];
  axil_r_observation_t branch_r_q[$];

  initial begin
    failed = 1'b0;
  end

  task automatic init_idle();
    failed = 1'b0;
    root_aw_q.delete();
    root_w_q.delete();
    root_ar_q.delete();
    root_b_q.delete();
    root_r_q.delete();
    trunk_aw_q.delete();
    trunk_w_q.delete();
    trunk_ar_q.delete();
    trunk_b_q.delete();
    trunk_r_q.delete();
    branch_aw_q.delete();
    branch_w_q.delete();
    branch_ar_q.delete();
    branch_b_q.delete();
    branch_r_q.delete();
  endtask

  task automatic set_root_observations(
      input axil_aw_observation_t aw_q[$], input axil_w_observation_t w_q[$],
      input axil_ar_observation_t ar_q[$], input axil_b_observation_t b_q[$],
      input axil_r_observation_t r_q[$]);
    root_aw_q = aw_q;
    root_w_q  = w_q;
    root_ar_q = ar_q;
    root_b_q  = b_q;
    root_r_q  = r_q;
  endtask

  task automatic set_trunk_observations(
      input axil_aw_observation_t aw_q[$], input axil_w_observation_t w_q[$],
      input axil_ar_observation_t ar_q[$], input axil_b_observation_t b_q[$],
      input axil_r_observation_t r_q[$]);
    trunk_aw_q = aw_q;
    trunk_w_q  = w_q;
    trunk_ar_q = ar_q;
    trunk_b_q  = b_q;
    trunk_r_q  = r_q;
  endtask

  task automatic set_branch_observations(
      input axil_aw_observation_t aw_q[$], input axil_w_observation_t w_q[$],
      input axil_ar_observation_t ar_q[$], input axil_b_observation_t b_q[$],
      input axil_r_observation_t r_q[$]);
    branch_aw_q = aw_q;
    branch_w_q  = w_q;
    branch_ar_q = ar_q;
    branch_b_q  = b_q;
    branch_r_q  = r_q;
  endtask

  task automatic report_failure(input string message);
    failed = 1'b1;
    $error("%s", message);
  endtask

  task automatic report_mismatch(input string message, inout int mismatch_count);
    mismatch_count++;
    report_failure(message);
  endtask

  task automatic check_count(input string stream_name, input int expected_count,
                             input int observed_count, inout logic sizes_match);
    if (observed_count != expected_count) begin
      sizes_match = 1'b0;
      report_failure($sformatf(
                     "%s count mismatch: expected %0d observed %0d",
                     stream_name,
                     expected_count,
                     observed_count
                     ));
    end
  endtask

  // For overlapping ranges, the first match is only used to classify the address as branch.
  function automatic int branch_range_index(
      input logic [AxilAddrWidth-1:0] addr,
      input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_start_addr,
      input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_end_addr);
    branch_range_index = -1;
    for (int i = 0; i < NumBranchAddrRanges; i++) begin
      if (addr >= branch_start_addr[i] && addr <= branch_end_addr[i]) return i;
    end
  endfunction

  function automatic logic aw_matches(input axil_aw_t packet,
                                      input logic [AxilAddrWidth-1:0] expected_addr,
                                      input axil_split_transaction_t expected);
    aw_matches = packet.addr === expected_addr && packet.prot === expected.prot &&
        packet.user === expected.addr_user;
  endfunction

  function automatic logic w_matches(input axil_w_t packet,
                                     input axil_split_transaction_t expected);
    w_matches = packet.data === expected.data && packet.strb === expected.strb &&
        packet.user === expected.data_user;
  endfunction

  function automatic logic ar_matches(input axil_ar_t packet,
                                      input logic [AxilAddrWidth-1:0] expected_addr,
                                      input axil_split_transaction_t expected);
    ar_matches = packet.addr === expected_addr && packet.prot === expected.prot &&
        packet.user === expected.addr_user;
  endfunction

  function automatic logic b_matches(input axil_b_t packet,
                                     input axil_split_transaction_t expected);
    b_matches = packet.resp === expected.resp;
  endfunction

  function automatic logic r_matches(input axil_r_t packet,
                                     input axil_split_transaction_t expected);
    r_matches = packet.data === expected.data && packet.resp === expected.resp &&
        packet.user === expected.response_user;
  endfunction

  function automatic logic [AxilAddrWidth-1:0] routed_branch_addr(
      input logic [AxilAddrWidth-1:0] root_addr,
      input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_start_addr);
    routed_branch_addr = NormalizeBranchAddress ? root_addr - branch_start_addr[0] : root_addr;
  endfunction

  // Root AW/W and AR streams are independent, so prediction first builds write/read transactions
  // separately and then merges them by accepted-request timestamp.
  task automatic predict_transactions(
      input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_start_addr,
      input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_end_addr,
      input axil_aw_observation_t root_aw_q[$], input axil_w_observation_t root_w_q[$],
      input axil_ar_observation_t root_ar_q[$], input axil_b_observation_t root_b_q[$],
      input axil_r_observation_t root_r_q[$], output axil_split_transaction_t exp_q[$],
      output logic prediction_valid);
    axil_split_transaction_t write_q[$];
    axil_split_transaction_t read_q[$];
    int write_index = 0;
    int read_index = 0;

    exp_q.delete();
    prediction_valid = 1'b1;

    if (root_aw_q.size() != root_w_q.size() ||
        root_aw_q.size() != root_b_q.size() ||
        root_ar_q.size() != root_r_q.size()) begin
      prediction_valid = 1'b0;
      return;
    end

    for (int i = 0; i < root_aw_q.size(); i++) begin
      axil_split_transaction_t transaction;
      logic [AxilAddrWidth-1:0] root_addr = AxilAddrWidth'(root_aw_q[i].packet.addr);
      int range_index = branch_range_index(root_addr, branch_start_addr, branch_end_addr);

      transaction = '0;
      transaction.kind = AxilSplitTransactionWrite;
      transaction.route = (range_index >= 0) ? AxilSplitRouteBranch : AxilSplitRouteTrunk;
      transaction.root_addr = root_aw_q[i].packet.addr;
      transaction.routed_addr = (transaction.route == AxilSplitRouteBranch) ?
          AxilAddrWidth'(routed_branch_addr(root_addr, branch_start_addr)) :
          root_aw_q[i].packet.addr;
      transaction.prot = root_aw_q[i].packet.prot;
      transaction.addr_user = root_aw_q[i].packet.user;
      transaction.data = root_w_q[i].packet.data;
      transaction.strb = root_w_q[i].packet.strb;
      transaction.data_user = root_w_q[i].packet.user;
      transaction.resp = root_b_q[i].packet.resp;
      transaction.request_ts = `BR_SIM_MAX(root_aw_q[i].timestamp, root_w_q[i].timestamp);
      transaction.response_ts = root_b_q[i].timestamp;
      write_q.push_back(transaction);
    end

    for (int i = 0; i < root_ar_q.size(); i++) begin
      axil_split_transaction_t transaction;
      logic [AxilAddrWidth-1:0] root_addr = AxilAddrWidth'(root_ar_q[i].packet.addr);
      int range_index = branch_range_index(root_addr, branch_start_addr, branch_end_addr);

      transaction = '0;
      transaction.kind = AxilSplitTransactionRead;
      transaction.route = (range_index >= 0) ? AxilSplitRouteBranch : AxilSplitRouteTrunk;
      transaction.root_addr = root_ar_q[i].packet.addr;
      transaction.routed_addr = (transaction.route == AxilSplitRouteBranch) ?
          AxilAddrWidth'(routed_branch_addr(root_addr, branch_start_addr)) :
          root_ar_q[i].packet.addr;
      transaction.prot = root_ar_q[i].packet.prot;
      transaction.addr_user = root_ar_q[i].packet.user;
      transaction.data = root_r_q[i].packet.data;
      transaction.resp = root_r_q[i].packet.resp;
      transaction.response_user = root_r_q[i].packet.user;
      transaction.request_ts = root_ar_q[i].timestamp;
      transaction.response_ts = root_r_q[i].timestamp;
      read_q.push_back(transaction);
    end

    while (write_index < write_q.size() || read_index < read_q.size()) begin
      logic is_write;

      if (write_index >= write_q.size()) is_write = 1'b0;
      else if (read_index >= read_q.size()) is_write = 1'b1;
      else is_write = write_q[write_index].request_ts <= read_q[read_index].request_ts;

      if (is_write) begin
        exp_q.push_back(write_q[write_index]);
        write_index++;
      end else begin
        exp_q.push_back(read_q[read_index]);
        read_index++;
      end
    end
  endtask

  task automatic check_root_request_counts(
      input int expected_writes, input int expected_reads, input axil_aw_observation_t root_aw_q[$],
      input axil_w_observation_t root_w_q[$], input axil_ar_observation_t root_ar_q[$],
      inout logic sizes_match);
    check_count("Root AW request", expected_writes, root_aw_q.size(), sizes_match);
    check_count("Root W request", expected_writes, root_w_q.size(), sizes_match);
    check_count("Root AR request", expected_reads, root_ar_q.size(), sizes_match);
  endtask

  task automatic count_expected_transactions(input axil_split_transaction_t exp_q[$],
                                             output int trunk_writes, output int trunk_reads,
                                             output int branch_writes, output int branch_reads);
    trunk_writes  = 0;
    trunk_reads   = 0;
    branch_writes = 0;
    branch_reads  = 0;

    for (int i = 0; i < exp_q.size(); i++) begin
      logic is_write = exp_q[i].kind == AxilSplitTransactionWrite;
      logic is_branch = exp_q[i].route == AxilSplitRouteBranch;

      branch_writes += is_write && is_branch;
      trunk_writes += is_write && !is_branch;
      branch_reads += !is_write && is_branch;
      trunk_reads += !is_write && !is_branch;
    end
  endtask

  task automatic check_routed_request_counts(
      input axil_split_transaction_t exp_q[$], input axil_aw_observation_t trunk_aw_q[$],
      input axil_w_observation_t trunk_w_q[$], input axil_ar_observation_t trunk_ar_q[$],
      input axil_aw_observation_t branch_aw_q[$], input axil_w_observation_t branch_w_q[$],
      input axil_ar_observation_t branch_ar_q[$], inout logic sizes_match);
    int trunk_writes = 0;
    int trunk_reads = 0;
    int branch_writes = 0;
    int branch_reads = 0;

    count_expected_transactions(exp_q, trunk_writes, trunk_reads, branch_writes, branch_reads);

    check_count("Trunk AW request", trunk_writes, trunk_aw_q.size(), sizes_match);
    check_count("Trunk W request", trunk_writes, trunk_w_q.size(), sizes_match);
    check_count("Branch AW request", branch_writes, branch_aw_q.size(), sizes_match);
    check_count("Branch W request", branch_writes, branch_w_q.size(), sizes_match);
    check_count("Trunk read request", trunk_reads, trunk_ar_q.size(), sizes_match);
    check_count("Branch read request", branch_reads, branch_ar_q.size(), sizes_match);
  endtask

  task automatic check_response_counts(
      input axil_split_transaction_t exp_q[$], input axil_b_observation_t root_b_q[$],
      input axil_r_observation_t root_r_q[$], input axil_b_observation_t trunk_b_q[$],
      input axil_r_observation_t trunk_r_q[$], input axil_b_observation_t branch_b_q[$],
      input axil_r_observation_t branch_r_q[$], inout logic sizes_match);
    int writes;
    int reads;
    int trunk_writes = 0;
    int trunk_reads = 0;
    int branch_writes = 0;
    int branch_reads = 0;

    count_expected_transactions(exp_q, trunk_writes, trunk_reads, branch_writes, branch_reads);
    writes = trunk_writes + branch_writes;
    reads  = trunk_reads + branch_reads;

    check_count("Root B response", writes, root_b_q.size(), sizes_match);
    check_count("Root R response", reads, root_r_q.size(), sizes_match);
    check_count("Trunk B response", trunk_writes, trunk_b_q.size(), sizes_match);
    check_count("Branch B response", branch_writes, branch_b_q.size(), sizes_match);
    check_count("Trunk R response", trunk_reads, trunk_r_q.size(), sizes_match);
    check_count("Branch R response", branch_reads, branch_r_q.size(), sizes_match);
  endtask

  function automatic logic next_event_is_request(input time req_ts_q[$], input time resp_ts_q[$],
                                                 input int req_i, input int resp_i);
    if (resp_i >= resp_ts_q.size()) next_event_is_request = 1'b1;
    else if (req_i >= req_ts_q.size()) next_event_is_request = 1'b0;
    else next_event_is_request = req_ts_q[req_i] < resp_ts_q[resp_i];
  endfunction

  function automatic int max_outstanding(input time req_ts_q[$], input time resp_ts_q[$]);
    int req_i = 0;
    int resp_i = 0;
    int pending = 0;

    max_outstanding = 0;
    while (req_i + resp_i < req_ts_q.size() + resp_ts_q.size()) begin
      logic is_req = next_event_is_request(req_ts_q, resp_ts_q, req_i, resp_i);

      if (is_req) begin
        pending++;
        req_i++;
      end else begin
        pending--;
        resp_i++;
      end
      if (pending > max_outstanding) max_outstanding = pending;
    end
  endfunction

  // Walk request and response timestamps in order to measure the real outstanding depth, proving
  // the backpressure scenarios hit the configured limit instead of merely queueing traffic.
  task automatic check_outstanding_depths(
      input int exp_max_reads, input int exp_max_writes, input axil_ar_observation_t root_ar_q[$],
      input axil_r_observation_t root_r_q[$], input axil_aw_observation_t root_aw_q[$],
      input axil_b_observation_t root_b_q[$], inout int mismatch_count);
    time read_req_ts_q[$];
    time read_resp_ts_q[$];
    time write_req_ts_q[$];
    time write_resp_ts_q[$];
    int max_pending_reads;
    int max_pending_writes;

    for (int i = 0; i < root_ar_q.size(); i++) read_req_ts_q.push_back(root_ar_q[i].timestamp);
    for (int i = 0; i < root_r_q.size(); i++) read_resp_ts_q.push_back(root_r_q[i].timestamp);
    for (int i = 0; i < root_aw_q.size(); i++) write_req_ts_q.push_back(root_aw_q[i].timestamp);
    for (int i = 0; i < root_b_q.size(); i++) write_resp_ts_q.push_back(root_b_q[i].timestamp);
    max_pending_reads  = max_outstanding(read_req_ts_q, read_resp_ts_q);
    max_pending_writes = max_outstanding(write_req_ts_q, write_resp_ts_q);

    if (exp_max_reads > 0 && max_pending_reads != exp_max_reads) begin
      report_mismatch(
          $sformatf(
          "Read outstanding depth did not reach %0d; observed %0d", exp_max_reads, max_pending_reads
          ), mismatch_count);
    end
    if (exp_max_writes > 0 && max_pending_writes != exp_max_writes) begin
      report_mismatch($sformatf(
                      "Write outstanding depth did not reach %0d; observed %0d",
                      exp_max_writes,
                      max_pending_writes
                      ), mismatch_count);
    end
  endtask

  task automatic check_write_transaction(
      input axil_split_transaction_t expected_transaction, input axil_aw_observation_t root_aw,
      input axil_w_observation_t root_w, input axil_aw_observation_t routed_aw,
      input axil_w_observation_t routed_w, input axil_b_observation_t routed_b,
      input axil_b_observation_t root_b, input int write_index, inout int mismatch_count);
    if (!aw_matches(
            root_aw.packet, expected_transaction.root_addr, expected_transaction
        ) || !w_matches(
            root_w.packet, expected_transaction
        )) begin
      report_mismatch($sformatf("Root write transaction %0d payload mismatch", write_index),
                      mismatch_count);
    end
    if (!aw_matches(
            routed_aw.packet, expected_transaction.routed_addr, expected_transaction
        ) || !w_matches(
            routed_w.packet, expected_transaction
        )) begin
      report_mismatch($sformatf("Routed write transaction %0d payload mismatch", write_index),
                      mismatch_count);
    end
    if (!b_matches(
            routed_b.packet, expected_transaction
        ) || !b_matches(
            root_b.packet, expected_transaction
        )) begin
      report_mismatch($sformatf("Write transaction %0d response mismatch", write_index),
                      mismatch_count);
    end
  endtask

  task automatic check_read_transaction(
      input axil_split_transaction_t expected_transaction, input axil_ar_observation_t root_ar,
      input axil_ar_observation_t routed_ar, input axil_r_observation_t routed_r,
      input axil_r_observation_t root_r, input int read_index, inout int mismatch_count);
    if (!ar_matches(root_ar.packet, expected_transaction.root_addr, expected_transaction)) begin
      report_mismatch($sformatf("Root read transaction %0d payload mismatch", read_index),
                      mismatch_count);
    end
    if (!ar_matches(routed_ar.packet, expected_transaction.routed_addr, expected_transaction)) begin
      report_mismatch($sformatf("Routed read transaction %0d payload mismatch", read_index),
                      mismatch_count);
    end
    if (!r_matches(
            routed_r.packet, expected_transaction
        ) || !r_matches(
            root_r.packet, expected_transaction
        )) begin
      report_mismatch($sformatf("Read transaction %0d response mismatch", read_index),
                      mismatch_count);
    end
  endtask

  // Route switching is legal only after the previous route's outstanding responses have drained.
  // Reads and writes are tracked independently because the DUT has separate outstanding limits.
  task automatic check_route_switching_rules(input axil_split_transaction_t exp_q[$],
                                             inout int mismatch_count);
    axil_split_route_t active_read_route;
    axil_split_route_t active_write_route;
    logic              read_route_active = 1'b0;
    logic              write_route_active = 1'b0;
    time               read_route_drain_ts = 0;
    time               write_route_drain_ts = 0;

    for (int i = 0; i < exp_q.size(); i++) begin
      axil_split_transaction_t transaction = exp_q[i];

      if (transaction.kind == AxilSplitTransactionRead) begin
        if (read_route_active && transaction.route != active_read_route &&
            transaction.request_ts <= read_route_drain_ts) begin
          report_mismatch(
              $sformatf(
              "Read route switched before outstanding responses drained at transaction %0d", i),
              mismatch_count);
        end
        active_read_route = transaction.route;
        read_route_active = 1'b1;
        if (transaction.response_ts > read_route_drain_ts) begin
          read_route_drain_ts = transaction.response_ts;
        end
      end else begin
        if (write_route_active && transaction.route != active_write_route &&
            transaction.request_ts <= write_route_drain_ts) begin
          report_mismatch(
              $sformatf(
              "Write route switched before outstanding responses drained at transaction %0d", i),
              mismatch_count);
        end
        active_write_route = transaction.route;
        write_route_active = 1'b1;
        if (transaction.response_ts > write_route_drain_ts) begin
          write_route_drain_ts = transaction.response_ts;
        end
      end
    end
  endtask

  task automatic compare(input int expected_writes, input int expected_reads,
                         input int exp_max_reads, input int exp_max_writes,
                         input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_start_addr,
                         input logic [NumBranchAddrRanges-1:0][AxilAddrWidth-1:0] branch_end_addr);
    axil_split_transaction_t exp_q[$];
    logic sizes_match = 1'b1;
    logic prediction_valid;
    int mismatch_count = 0;
    int write_index = 0;
    int read_index = 0;
    int trunk_write_index = 0;
    int trunk_read_index = 0;
    int branch_write_index = 0;
    int branch_read_index = 0;

    check_root_request_counts(expected_writes, expected_reads, root_aw_q, root_w_q, root_ar_q,
                              sizes_match);
    predict_transactions(branch_start_addr, branch_end_addr, root_aw_q, root_w_q, root_ar_q,
                         root_b_q, root_r_q, exp_q, prediction_valid);
    if (!prediction_valid) begin
      report_failure("Root AXI-Lite observations cannot form complete split transactions");
      return;
    end

    check_routed_request_counts(exp_q, trunk_aw_q, trunk_w_q, trunk_ar_q, branch_aw_q, branch_w_q,
                                branch_ar_q, sizes_match);
    check_response_counts(exp_q, root_b_q, root_r_q, trunk_b_q, trunk_r_q, branch_b_q, branch_r_q,
                          sizes_match);
    if (!sizes_match) begin
      return;
    end

    for (int i = 0; i < exp_q.size(); i++) begin
      if (exp_q[i].kind == AxilSplitTransactionWrite) begin
        if (exp_q[i].route == AxilSplitRouteBranch) begin
          check_write_transaction(exp_q[i], root_aw_q[write_index], root_w_q[write_index],
                                  branch_aw_q[branch_write_index], branch_w_q[branch_write_index],
                                  branch_b_q[branch_write_index], root_b_q[write_index],
                                  write_index, mismatch_count);
          branch_write_index++;
        end else begin
          check_write_transaction(exp_q[i], root_aw_q[write_index], root_w_q[write_index],
                                  trunk_aw_q[trunk_write_index], trunk_w_q[trunk_write_index],
                                  trunk_b_q[trunk_write_index], root_b_q[write_index], write_index,
                                  mismatch_count);
          trunk_write_index++;
        end
        write_index++;
      end else begin
        if (exp_q[i].route == AxilSplitRouteBranch) begin
          check_read_transaction(exp_q[i], root_ar_q[read_index], branch_ar_q[branch_read_index],
                                 branch_r_q[branch_read_index], root_r_q[read_index], read_index,
                                 mismatch_count);
          branch_read_index++;
        end else begin
          check_read_transaction(exp_q[i], root_ar_q[read_index], trunk_ar_q[trunk_read_index],
                                 trunk_r_q[trunk_read_index], root_r_q[read_index], read_index,
                                 mismatch_count);
          trunk_read_index++;
        end
        read_index++;
      end
    end

    check_route_switching_rules(exp_q, mismatch_count);
    check_outstanding_depths(exp_max_reads, exp_max_writes, root_ar_q, root_r_q, root_aw_q,
                             root_b_q, mismatch_count);
    if (mismatch_count != 0) begin
      $error("br_amba_axil_split scoreboard found %0d mismatches", mismatch_count);
    end
  endtask
endmodule : br_amba_axil_split_scoreboard
