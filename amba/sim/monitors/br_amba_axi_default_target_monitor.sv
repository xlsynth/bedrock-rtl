// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

// AXI default-target response monitor.
//
// This is not a generic AXI bus monitor. It checks the specific
// br_amba_axi_default_target contract: writes respond only after both write
// channels are accepted, reads return the configured default data for each beat,
// response IDs match accepted request IDs, and all responses use the expected code.
module br_amba_axi_default_target_monitor #(
    parameter int DataWidth = 32,
    parameter int AxiIdWidth = 2,
    parameter bit SingleBeat = 0,
    parameter logic [AxiRespWidth-1:0] ExpectedResp = AxiRespDecerr,
    parameter logic [DataWidth-1:0] DefaultReadData = '0,
    parameter int TimeoutCycles = 100,
    localparam int AxiLenWidth = SingleBeat ? 1 : AxiBurstLenWidth
) (
    input logic clk,
    input logic rst,

    input logic target_awvalid,
    input logic target_awready,
    input logic [AxiIdWidth-1:0] target_awid,
    input logic [AxiLenWidth-1:0] target_awlen,
    input logic target_wvalid,
    input logic target_wready,
    input logic target_wlast,
    input logic [AxiIdWidth-1:0] target_bid,
    input logic [AxiRespWidth-1:0] target_bresp,
    input logic target_bvalid,
    input logic target_bready,
    input logic target_arvalid,
    input logic target_arready,
    input logic [AxiIdWidth-1:0] target_arid,
    input logic [AxiLenWidth-1:0] target_arlen,
    input logic [DataWidth-1:0] target_rdata,
    input logic [AxiRespWidth-1:0] target_rresp,
    input logic [AxiIdWidth-1:0] target_rid,
    input logic target_rlast,
    input logic target_rvalid,
    input logic target_rready,

    output logic failed
);

  typedef struct packed {
    logic [AxiIdWidth-1:0]  id;
    logic [AxiLenWidth-1:0] len;
  } axi_read_request_t;

  task automatic check(input logic condition, input string message = "Check failed");
    if (!condition) begin
      failed = 1'b1;
      $error("%s", message);
    end
  endtask

  task automatic init_idle();
    failed = 1'b0;
  endtask

  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  task automatic monitor_write_responses(input int num_writes);
    logic [AxiIdWidth-1:0] aw_queue[$];
    logic [AxiIdWidth-1:0] expected_id;
    int unsigned w_count;
    int completed;
    int timeout;

    w_count   = 0;
    completed = 0;
    timeout   = TimeoutCycles;

    while (completed < num_writes && timeout > 0) begin
      @(posedge clk);
      if (target_awvalid && target_awready) begin
        aw_queue.push_back(target_awid);
      end
      if (target_wvalid && target_wready) begin
        check(target_wlast, "W accepted without WLAST");
        w_count++;
      end
      if (target_bvalid) begin
        check(aw_queue.size() > 0 && w_count > 0,
              "B valid asserted before write address and final data were accepted");
      end
      if (target_bvalid && target_bready) begin
        check(aw_queue.size() > 0, "B response without expected AW request");
        check(w_count > 0, "B response without expected WLAST transfer");
        if (aw_queue.size() > 0) begin
          expected_id = aw_queue.pop_front();
        end
        if (w_count > 0) begin
          w_count--;
        end
        check(target_bid === expected_id, $sformatf(
              "%s: expected 0x%0h got 0x%0h", "B ID mismatch", expected_id, target_bid));
        check(target_bresp === ExpectedResp, $sformatf(
              "%s: expected 0x%0h got 0x%0h", "B response mismatch", ExpectedResp, target_bresp));
        completed++;
      end
      timeout--;
    end

    check(completed == num_writes, "Timeout waiting for B responses");
    check(aw_queue.size() == 0, "Write monitor AW queue not empty");
    check(w_count == 0, "Write monitor W count not empty");
    @(negedge clk);
    check(!target_bvalid, "B valid remained asserted after final response handshake");
  endtask

  task automatic monitor_read_responses(input int num_reads);
    axi_read_request_t queue[$];
    axi_read_request_t current;
    bit active;
    int unsigned beat;
    int completed;
    int timeout;

    timeout = TimeoutCycles;
    active = 1'b0;
    beat = 0;
    completed = 0;

    while (completed < num_reads && timeout > 0) begin
      @(posedge clk);
      if (target_arvalid && target_arready) begin
        queue.push_back('{id: target_arid, len: target_arlen});
      end
      if (target_rvalid && target_rready) begin
        if (!active) begin
          check(queue.size() > 0, "R transfer without expected AR request");
          if (queue.size() > 0) begin
            current = queue.pop_front();
            active = 1'b1;
            beat = 0;
          end
        end
        check(target_rid === current.id, $sformatf(
              "%s: expected 0x%0h got 0x%0h", "R ID mismatch", current.id, target_rid));
        check(target_rdata === DefaultReadData, $sformatf(
              "%s: expected 0x%0h got 0x%0h", "R data mismatch", DefaultReadData, target_rdata));
        check(target_rresp === ExpectedResp, $sformatf(
              "%s: expected 0x%0h got 0x%0h", "R response mismatch", ExpectedResp, target_rresp));
        check(target_rlast === (beat == int'(current.len)), "R last mismatch");
        if (target_rlast) begin
          completed++;
          active = 1'b0;
        end else begin
          beat++;
        end
      end
      timeout--;
    end

    check(completed == num_reads, "Timeout waiting for R burst responses");
    check(queue.size() == 0, "Read monitor queue not empty");
    @(negedge clk);
    check(!target_rvalid, "R valid remained asserted after final response handshake");
  endtask

  task automatic run(input int num_writes = 0, input int num_reads = 0, input int awvalid_delay = 0,
                     input int wvalid_delay = 0);
    fork
      begin
        if (num_writes > 0) begin
          monitor_write_responses(num_writes);
        end
      end
      begin
        if (num_reads > 0) begin
          monitor_read_responses(num_reads);
        end
      end
    join
  endtask

endmodule : br_amba_axi_default_target_monitor
