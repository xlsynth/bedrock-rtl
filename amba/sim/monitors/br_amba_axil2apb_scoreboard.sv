// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_apb_sim_pkg::*;
import br_amba_axil_sim_pkg::*;
import br_amba_axil_monitor_sim_pkg::*;
import br_amba_axil2apb_sim_pkg::*;
import br_amba_sim_pkg::*;

`include "br_amba_sim_macros.svh"

// br_amba_axil2apb scoreboard.
//
// The scoreboard predicts a protocol-agnostic expected transaction stream from
// accepted AXI-Lite requests and the APB response policy driven by the testbench.
// It then checks that each expected transaction is visible on both protocol
// sides: accepted AXI-Lite request channels, completed APB transfers, and
// returned AXI-Lite responses.
module br_amba_axil2apb_scoreboard #(
    parameter int ClockPeriodNs = 10
) (
    output logic failed
);

  task automatic init_idle();
    failed = 1'b0;
  endtask

  function automatic apb_transfer_t expected_apb_transfer(input axil2apb_transaction_t transaction);
    expected_apb_transfer = '0;
    expected_apb_transfer.addr = transaction.addr;
    expected_apb_transfer.prot = transaction.prot;
    expected_apb_transfer.strb = transaction.strb;
    expected_apb_transfer.write = transaction.kind == Axil2ApbTransactionWrite;
    expected_apb_transfer.data = transaction.data;
    expected_apb_transfer.slverr = transaction.slverr;
  endfunction

  function automatic axil_b_t expected_b_response(input axil2apb_transaction_t transaction);
    expected_b_response = '0;
    expected_b_response.resp = transaction.slverr ? AxiRespSlverr : AxiRespOkay;
  endfunction

  function automatic axil_r_t expected_r_response(input axil2apb_transaction_t transaction);
    expected_r_response = '0;
    expected_r_response.data = AxilDataWidth'(transaction.data);
    expected_r_response.resp = transaction.slverr ? AxiRespSlverr : AxiRespOkay;
  endfunction

  function automatic axil2apb_transaction_t predict_write_transaction(
      input axil_aw_t aw, input axil_w_t w, input apb_response_t response);
    predict_write_transaction.kind   = Axil2ApbTransactionWrite;
    predict_write_transaction.addr   = ApbAddrWidth'(aw.addr);
    predict_write_transaction.prot   = aw.prot;
    predict_write_transaction.strb   = ApbStrbWidth'(w.strb);
    predict_write_transaction.data   = ApbDataWidth'(w.data);
    predict_write_transaction.slverr = response.slverr;
  endfunction

  function automatic axil2apb_transaction_t predict_read_transaction(input axil_ar_t ar,
                                                                     input apb_response_t response);
    predict_read_transaction.kind   = Axil2ApbTransactionRead;
    predict_read_transaction.addr   = ApbAddrWidth'(ar.addr);
    predict_read_transaction.prot   = ar.prot;
    predict_read_transaction.strb   = '0;
    predict_read_transaction.data   = ApbDataWidth'(response.rdata);
    predict_read_transaction.slverr = response.slverr;
  endfunction

  task automatic check_queue_sizes(input int expected_size, input int observed_size,
                                   input string channel_name, inout logic sizes_match);
    if (expected_size != observed_size) begin
      failed = 1'b1;
      sizes_match = 1'b0;
      $error("%s queue size mismatch: expected %0d observed %0d", channel_name, expected_size,
             observed_size);
    end
  endtask

  task automatic predict_transactions(
      input axil_aw_observation_t observed_aw_queue[$],
      input axil_w_observation_t observed_w_queue[$],
      input axil_ar_observation_t observed_ar_queue[$], input apb_response_t response_queue[$],
      output axil2apb_transaction_t expected_transaction_queue[$], output logic prediction_valid);
    int   write_index = 0;
    int   read_index = 0;
    int   response_index = 0;
    logic last_read_grant = 1'b0;

    expected_transaction_queue.delete();
    prediction_valid = 1'b1;

    while ((write_index < observed_aw_queue.size() && write_index < observed_w_queue.size()) ||
           read_index < observed_ar_queue.size()) begin
      logic has_write = write_index < observed_aw_queue.size() &&
                        write_index < observed_w_queue.size();
      logic has_read = read_index < observed_ar_queue.size();
      time write_timestamp;
      time read_timestamp;
      logic choose_read;

      if (response_index >= response_queue.size()) begin
        failed = 1'b1;
        prediction_valid = 1'b0;
        $error("The test did not provide enough APB responses for the observed AXI-Lite traffic");
        return;
      end

      write_timestamp = has_write ? (observed_aw_queue[write_index].timestamp >
              observed_w_queue[write_index].timestamp ? observed_aw_queue[write_index].timestamp :
              observed_w_queue[write_index].timestamp) : 0;
      read_timestamp = has_read ? observed_ar_queue[read_index].timestamp : 0;

      // Writes become eligible only after both AW and W handshakes. If read and
      // write requests become eligible in the same sampled cycle, match the
      // bridge's round-robin state: read has reset priority, then the previous
      // grant becomes lowest priority.
      if (has_read && has_write && read_timestamp == write_timestamp) begin
        choose_read = !last_read_grant;
      end else begin
        choose_read = has_read && (!has_write || read_timestamp < write_timestamp);
      end

      if (choose_read) begin
        expected_transaction_queue.push_back(
            predict_read_transaction(
            observed_ar_queue[read_index].packet, response_queue[response_index]));
        read_index++;
        last_read_grant = 1'b1;
      end else begin
        expected_transaction_queue.push_back(predict_write_transaction(
                                             observed_aw_queue[write_index].packet,
                                             observed_w_queue[write_index].packet,
                                             response_queue[response_index]
                                             ));
        write_index++;
        last_read_grant = 1'b0;
      end
      response_index++;
    end

    if (response_index != response_queue.size()) begin
      failed = 1'b1;
      prediction_valid = 1'b0;
      $error(
          "The test provided %0d APB responses, but only %0d AXI-Lite transactions were observed",
          response_queue.size(), response_index);
    end
  endtask

  task automatic check_apb_transfer(input axil2apb_transaction_t expected_transaction,
                                    input apb_transfer_observation_t observed_transfer,
                                    input int transaction_index, inout int mismatch_count);
    apb_transfer_t expected_transfer = expected_apb_transfer(expected_transaction);

    if (observed_transfer.packet !== expected_transfer) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_transfer.packet, expected_transfer, $sformatf(
                          "APB transfer mismatch at transaction %0d", transaction_index), failed);
  endtask

  task automatic check_write_apb_timing(
      input apb_transfer_observation_t observed_apb, input axil_aw_observation_t observed_aw,
      input axil_w_observation_t observed_w, input int write_index, inout int mismatch_count);
    time request_timestamp;
    time expected_apb_timestamp;

    request_timestamp = observed_aw.timestamp > observed_w.timestamp ? observed_aw.timestamp :
                                                                     observed_w.timestamp;
    expected_apb_timestamp = request_timestamp + ClockPeriodNs;
    if (observed_apb.request_timestamp != expected_apb_timestamp) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_apb.request_timestamp, expected_apb_timestamp, $sformatf(
                          {
                            "APB write request %0d was not observed one clock after ",
                            "AXI-Lite AW/W completed"
                          },
                          write_index
                          ), failed);
  endtask

  task automatic check_read_apb_timing(input apb_transfer_observation_t observed_apb,
                                       input axil_ar_observation_t observed_ar,
                                       input int read_index, inout int mismatch_count);
    time expected_apb_timestamp = observed_ar.timestamp + ClockPeriodNs;

    if (observed_apb.request_timestamp != expected_apb_timestamp) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_apb.request_timestamp, expected_apb_timestamp, $sformatf(
                          {
                            "APB read request %0d was not observed one clock after ",
                            "AXI-Lite AR completed"
                          },
                          read_index
                          ), failed);
  endtask

  task automatic check_write_request(
      input axil2apb_transaction_t expected_transaction, input axil_aw_observation_t observed_aw,
      input axil_w_observation_t observed_w, input int write_index, inout int mismatch_count);
    axil_aw_t expected_aw;
    axil_w_t  expected_w;

    expected_aw = '0;
    expected_aw.addr = AxilAddrWidth'(expected_transaction.addr);
    expected_aw.prot = expected_transaction.prot;

    expected_w = '0;
    expected_w.data = AxilDataWidth'(expected_transaction.data);
    expected_w.strb = AxilStrobeWidth'(expected_transaction.strb);

    if (observed_aw.packet !== expected_aw) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_aw.packet, expected_aw, $sformatf(
                          "AXI-Lite AW request mismatch at write %0d", write_index), failed);
    if (observed_w.packet !== expected_w) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_w.packet, expected_w, $sformatf(
                          "AXI-Lite W request mismatch at write %0d", write_index), failed);
  endtask

  task automatic check_read_request(input axil2apb_transaction_t expected_transaction,
                                    input axil_ar_observation_t observed_ar, input int read_index,
                                    inout int mismatch_count);
    axil_ar_t expected_ar;

    expected_ar = '0;
    expected_ar.addr = AxilAddrWidth'(expected_transaction.addr);
    expected_ar.prot = expected_transaction.prot;

    if (observed_ar.packet !== expected_ar) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_ar.packet, expected_ar, $sformatf(
                          "AXI-Lite AR request mismatch at read %0d", read_index), failed);
  endtask

  task automatic check_write_response(input axil2apb_transaction_t expected_transaction,
                                      input apb_transfer_observation_t observed_apb,
                                      input axil_b_observation_t observed_b, input int write_index,
                                      inout int mismatch_count);
    axil_b_t expected_b = expected_b_response(expected_transaction);
    time expected_bvalid_timestamp = observed_apb.completion_timestamp + ClockPeriodNs;

    if (expected_b !== observed_b.packet) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_b.packet, expected_b, $sformatf(
                          "AXI-Lite B response mismatch at write %0d", write_index), failed);

    if (observed_b.valid_timestamp != expected_bvalid_timestamp) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_b.valid_timestamp, expected_bvalid_timestamp, $sformatf(
                          {
                            "AXI-Lite BVALID at write %0d was not observed one clock ",
                            "after APB completion"
                          },
                          write_index
                          ), failed);

    if (observed_b.timestamp < observed_b.valid_timestamp) begin
      failed = 1'b1;
      mismatch_count++;
      $error("AXI-Lite B handshake at write %0d was observed before BVALID: b=%0t bvalid=%0t",
             write_index, observed_b.timestamp, observed_b.valid_timestamp);
    end
  endtask

  task automatic check_read_response(input axil2apb_transaction_t expected_transaction,
                                     input apb_transfer_observation_t observed_apb,
                                     input axil_r_observation_t observed_r, input int read_index,
                                     inout int mismatch_count);
    axil_r_t expected_r = expected_r_response(expected_transaction);
    time expected_rvalid_timestamp = observed_apb.completion_timestamp + ClockPeriodNs;

    if (expected_r !== observed_r.packet) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_r.packet, expected_r, $sformatf(
                          "AXI-Lite R response mismatch at read %0d", read_index), failed);

    if (observed_r.valid_timestamp != expected_rvalid_timestamp) begin
      mismatch_count++;
    end
    `BR_AMBA_SIM_CHECK_EQ(observed_r.valid_timestamp, expected_rvalid_timestamp, $sformatf(
                          {
                            "AXI-Lite RVALID at read %0d was not observed one clock ",
                            "after APB completion"
                          },
                          read_index
                          ), failed);

    if (observed_r.timestamp < observed_r.valid_timestamp) begin
      failed = 1'b1;
      mismatch_count++;
      $error("AXI-Lite R handshake at read %0d was observed before RVALID: r=%0t rvalid=%0t",
             read_index, observed_r.timestamp, observed_r.valid_timestamp);
    end
  endtask

  task automatic check_read_write_priority(
      input axil_request_state_observation_t observed_request_state_queue[$],
      input axil2apb_transaction_t expected_transaction_queue[$],
      input axil_b_observation_t observed_b_queue[$],
      input axil_r_observation_t observed_r_queue[$], inout int mismatch_count);
    logic last_read_grant = 1'b0;
    time  bridge_available_timestamp = 0;
    int   transaction_index = 0;
    int   write_response_index = 0;
    int   read_response_index = 0;

    foreach (observed_request_state_queue[i]) begin
      axil_request_state_observation_t request_state = observed_request_state_queue[i];
      logic write_eligible = request_state.awvalid && request_state.wvalid;
      logic read_eligible = request_state.arvalid;
      logic write_grant = request_state.awready && request_state.wready;
      logic read_grant = request_state.arready;

      if (request_state.timestamp >= bridge_available_timestamp && (write_eligible ||
                                                                    read_eligible)) begin
        logic expect_read_grant = read_eligible && (!write_eligible || !last_read_grant);
        logic expect_write_grant = write_eligible && (!read_eligible || last_read_grant);

        if (expect_read_grant && (!read_grant || write_grant)) begin
          failed = 1'b1;
          mismatch_count++;
          $error("AXI-Lite arbitration mismatch at %0t: expected read grant",
                 request_state.timestamp);
        end else if (expect_write_grant && (!write_grant || read_grant)) begin
          failed = 1'b1;
          mismatch_count++;
          $error("AXI-Lite arbitration mismatch at %0t: expected write grant",
                 request_state.timestamp);
        end
      end

      if (!read_grant && !write_grant) begin
        continue;
      end

      if (request_state.timestamp < bridge_available_timestamp) begin
        failed = 1'b1;
        mismatch_count++;
        $error("AXI-Lite grant observed before the bridge completed the previous transaction");
        continue;
      end else if (read_grant && write_grant) begin
        failed = 1'b1;
        mismatch_count++;
        $error("AXI-Lite read and write grants were observed in the same cycle");
        continue;
      end else if (transaction_index >= expected_transaction_queue.size()) begin
        failed = 1'b1;
        mismatch_count++;
        $error("AXI-Lite grant observed after all expected bridge transactions were complete");
        continue;
      end else if (write_grant &&
                   expected_transaction_queue[transaction_index].kind !=
                       Axil2ApbTransactionWrite) begin
        failed = 1'b1;
        mismatch_count++;
        $error("AXI-Lite write grant observed when the scoreboard expected a read grant");
        continue;
      end else if (read_grant &&
                   expected_transaction_queue[transaction_index].kind !=
                       Axil2ApbTransactionRead) begin
        failed = 1'b1;
        mismatch_count++;
        $error("AXI-Lite read grant observed when the scoreboard expected a write grant");
        continue;
      end

      if (write_grant) begin
        if (write_response_index >= observed_b_queue.size()) begin
          failed = 1'b1;
          mismatch_count++;
          $error("AXI-Lite write grant at %0t did not produce a matching B response",
                 request_state.timestamp);
          continue;
        end
        bridge_available_timestamp = observed_b_queue[write_response_index].timestamp +
                                     ClockPeriodNs;
        write_response_index++;
        last_read_grant = 1'b0;
      end else begin
        if (read_response_index >= observed_r_queue.size()) begin
          failed = 1'b1;
          mismatch_count++;
          $error("AXI-Lite read grant at %0t did not produce a matching R response",
                 request_state.timestamp);
          continue;
        end
        bridge_available_timestamp = observed_r_queue[read_response_index].timestamp +
                                     ClockPeriodNs;
        read_response_index++;
        last_read_grant = 1'b1;
      end
      transaction_index++;
    end
  endtask

  task automatic compare(input axil_request_state_observation_t observed_request_state_queue[$],
                         input axil_aw_observation_t observed_aw_queue[$],
                         input axil_w_observation_t observed_w_queue[$],
                         input axil_ar_observation_t observed_ar_queue[$],
                         input apb_response_t response_queue[$],
                         input apb_transfer_observation_t observed_apb_queue[$],
                         input axil_b_observation_t observed_b_queue[$],
                         input axil_r_observation_t observed_r_queue[$]);
    axil2apb_transaction_t expected_transaction_queue[$];
    int expected_write_count = 0;
    int expected_read_count = 0;
    int write_index = 0;
    int read_index = 0;
    int mismatch_count = 0;
    logic sizes_match = 1'b1;
    logic prediction_valid;

    check_queue_sizes(observed_aw_queue.size(), observed_w_queue.size(),
                      "AXI-Lite AW/W write request", sizes_match);
    if (!sizes_match) begin
      return;
    end

    predict_transactions(observed_aw_queue, observed_w_queue, observed_ar_queue, response_queue,
                         expected_transaction_queue, prediction_valid);
    if (!prediction_valid) begin
      return;
    end

    foreach (expected_transaction_queue[i]) begin
      if (expected_transaction_queue[i].kind == Axil2ApbTransactionWrite) begin
        expected_write_count++;
      end else begin
        expected_read_count++;
      end
    end

    check_queue_sizes(expected_transaction_queue.size(), observed_apb_queue.size(), "APB transfer",
                      sizes_match);
    check_queue_sizes(expected_write_count, observed_aw_queue.size(), "AXI-Lite AW request",
                      sizes_match);
    check_queue_sizes(expected_write_count, observed_w_queue.size(), "AXI-Lite W request",
                      sizes_match);
    check_queue_sizes(expected_write_count, observed_b_queue.size(), "AXI-Lite B response",
                      sizes_match);
    check_queue_sizes(expected_read_count, observed_ar_queue.size(), "AXI-Lite AR request",
                      sizes_match);
    check_queue_sizes(expected_read_count, observed_r_queue.size(), "AXI-Lite R response",
                      sizes_match);
    if (!sizes_match) begin
      return;
    end

    check_read_write_priority(observed_request_state_queue, expected_transaction_queue,
                              observed_b_queue, observed_r_queue, mismatch_count);

    foreach (expected_transaction_queue[transaction_index]) begin
      axil2apb_transaction_t expected_transaction;

      expected_transaction = expected_transaction_queue[transaction_index];
      check_apb_transfer(expected_transaction, observed_apb_queue[transaction_index],
                         transaction_index, mismatch_count);

      if (expected_transaction.kind == Axil2ApbTransactionWrite) begin
        check_write_request(expected_transaction, observed_aw_queue[write_index],
                            observed_w_queue[write_index], write_index, mismatch_count);
        check_write_apb_timing(observed_apb_queue[transaction_index],
                               observed_aw_queue[write_index], observed_w_queue[write_index],
                               write_index, mismatch_count);
        check_write_response(expected_transaction, observed_apb_queue[transaction_index],
                             observed_b_queue[write_index], write_index, mismatch_count);
        write_index++;
      end else begin
        check_read_request(expected_transaction, observed_ar_queue[read_index], read_index,
                           mismatch_count);
        check_read_apb_timing(observed_apb_queue[transaction_index], observed_ar_queue[read_index],
                              read_index, mismatch_count);
        check_read_response(expected_transaction, observed_apb_queue[transaction_index],
                            observed_r_queue[read_index], read_index, mismatch_count);
        read_index++;
      end
    end

    if (mismatch_count != 0) begin
      $error("br_amba_axil2apb scoreboard found %0d item mismatches", mismatch_count);
    end
  endtask
endmodule : br_amba_axil2apb_scoreboard
