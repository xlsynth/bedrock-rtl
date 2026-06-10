// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

// AXI-Lite default-target response monitor.
//
// This is not a generic AXI-Lite bus monitor. It checks the specific
// br_amba_axil_default_target contract: writes respond only after both write channels
// are accepted, reads return the configured default data, and all responses use the
// expected response code.
module br_amba_axil_monitor #(
    parameter int DataWidth = 32,
    parameter logic [AxiRespWidth-1:0] ExpectedResp = AxiRespDecerr,
    parameter logic [DataWidth-1:0] DefaultReadData = '0
) (
    input logic clk,
    input logic rst,

    input logic target_awvalid,
    input logic target_awready,
    input logic target_wvalid,
    input logic target_wready,
    input logic [AxiRespWidth-1:0] target_bresp,
    input logic target_bvalid,
    input logic target_bready,
    input logic target_arvalid,
    input logic target_arready,
    input logic [DataWidth-1:0] target_rdata,
    input logic [AxiRespWidth-1:0] target_rresp,
    input logic target_rvalid,
    input logic target_rready,

    output logic failed
);

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

  task automatic check_no_bvalid_after_first_write_channel(input int awvalid_delay,
                                                           input int wvalid_delay);
    if (awvalid_delay < wvalid_delay) begin
      wait (target_awvalid && target_awready);
      wait_cycles();
      check(!target_bvalid, "B valid asserted before write data was accepted");
    end else if (wvalid_delay < awvalid_delay) begin
      wait (target_wvalid && target_wready);
      wait_cycles();
      check(!target_bvalid, "B valid asserted before write address was accepted");
    end
  endtask

  task automatic monitor_b_response(input bit is_final);
    // Wait for a completed B-channel transfer before checking the sampled response.
    @(posedge clk);
    while (!(target_bvalid && target_bready)) begin
      @(posedge clk);
    end

    check(target_bresp === ExpectedResp, $sformatf(
          "%s: expected 0x%0h got 0x%0h", "B response mismatch", ExpectedResp, target_bresp));
    if (is_final) begin
      @(negedge clk);
      check(!target_bvalid, "B valid remained asserted after final response handshake");
    end
  endtask

  task automatic monitor_r_response(input bit is_final);
    // Wait for a completed R-channel transfer before checking response and read data.
    @(posedge clk);
    while (!(target_rvalid && target_rready)) begin
      @(posedge clk);
    end

    check(target_rresp === ExpectedResp, $sformatf(
          "%s: expected 0x%0h got 0x%0h", "R response mismatch", ExpectedResp, target_rresp));
    check(target_rdata === DefaultReadData, $sformatf(
          "%s: expected 0x%0h got 0x%0h", "R data mismatch", DefaultReadData, target_rdata));
    if (is_final) begin
      @(negedge clk);
      check(!target_rvalid, "R valid remained asserted after final response handshake");
    end
  endtask

  task automatic run(input int num_writes = 0, input int num_reads = 0,
                     input int awvalid_delay = 0, input int wvalid_delay = 0);
    fork
      begin
        if (num_writes > 0) begin
          check_no_bvalid_after_first_write_channel(awvalid_delay, wvalid_delay);
          for (int i = 0; i < num_writes; i++) begin
            monitor_b_response(i == num_writes - 1);
          end
        end
      end
      begin
        if (num_reads > 0) begin
          for (int i = 0; i < num_reads; i++) begin
            monitor_r_response(i == num_reads - 1);
          end
        end
      end
    join
  endtask

endmodule : br_amba_axil_monitor
