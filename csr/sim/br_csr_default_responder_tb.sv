// SPDX-License-Identifier: Apache-2.0
//
// Directed and randomized unit tests for the CSR default responder.

module br_csr_default_responder_tb;
  parameter int AddrWidth = 16;
  parameter int DataWidth = 32;

  localparam int StrobeWidth = DataWidth / 8;
  localparam int NumRandomCycles = 32;

  logic clk;
  logic rst;

  logic req_valid;
  logic req_write;
  logic [AddrWidth-1:0] req_addr;
  logic [DataWidth-1:0] req_wdata;
  logic [StrobeWidth-1:0] req_wstrb;
  logic req_privileged;
  logic req_secure;
  logic req_abort;

  logic resp_valid;
  logic [DataWidth-1:0] resp_rdata;
  logic resp_slverr;
  logic resp_decerr;

  br_csr_default_responder #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth)
  ) dut (
      .clk,
      .rst,
      .req_valid,
      .req_write,
      .req_addr,
      .req_wdata,
      .req_wstrb,
      .req_privileged,
      .req_secure,
      .req_abort,
      .resp_valid,
      .resp_rdata,
      .resp_slverr,
      .resp_decerr
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_response(input logic expected_valid, input string scenario);
    td.check(resp_valid === expected_valid, {scenario, ": response valid mismatch"});
    td.check(resp_rdata == '0, {scenario, ": response read data should be zero"});
    td.check(!resp_slverr, {scenario, ": slave error should remain deasserted"});
    td.check(resp_decerr === expected_valid, {scenario, ": decode error mismatch"});
  endtask

  initial begin
    req_valid = 1'b0;
    req_write = 1'b0;
    req_addr = '0;
    req_wdata = '0;
    req_wstrb = '0;
    req_privileged = 1'b0;
    req_secure = 1'b0;
    req_abort = 1'b0;

    td.reset_dut();
    check_response(1'b0, "reset");

    $display("Checking idle requests and ignored request payload");
    req_write = 1'b1;
    req_addr = '1;
    req_wdata = '1;
    req_wstrb = '1;
    req_privileged = 1'b1;
    req_secure = 1'b1;
    td.wait_cycles(2);
    check_response(1'b0, "idle");

    $display("Checking one-cycle read-response latency");
    req_write = 1'b0;
    req_abort = 1'b0;
    req_valid = 1'b1;
    check_response(1'b0, "read before clock edge");
    td.wait_cycles();
    check_response(1'b1, "read response");
    req_valid = 1'b0;
    check_response(1'b1, "read response remains registered");
    td.wait_cycles();
    check_response(1'b0, "idle after read");

    $display("Checking write response with an in-flight abort");
    req_valid = 1'b1;
    req_write = 1'b1;
    td.wait_cycles();
    check_response(1'b1, "write response before abort");
    req_valid = 1'b0;
    req_abort = 1'b1;
    check_response(1'b1, "aborted write response");
    td.wait_cycles();
    check_response(1'b0, "idle after aborted write");
    req_abort = 1'b0;

    $display("Checking consecutive completed requests");
    for (int i = 0; i < 4; i++) begin
      req_valid = 1'b1;
      req_write = i[0];
      req_addr  = AddrWidth'(i);
      req_wdata = DataWidth'(i);
      td.wait_cycles();
      check_response(1'b1, "consecutive response");
      req_valid = 1'b0;
      td.wait_cycles();
      check_response(1'b0, "idle between consecutive requests");
    end
    req_valid = 1'b0;
    req_abort = 1'b0;
    td.wait_cycles();
    check_response(1'b0, "idle after consecutive requests");

    $display("Checking reset clears a pending response");
    req_valid = 1'b1;
    td.reset_dut();
    check_response(1'b0, "response during reset");
    req_valid = 1'b0;
    td.wait_cycles();
    check_response(1'b0, "idle after reset");

    $display("Checking randomized request, payload, and abort combinations");
    for (int i = 0; i < NumRandomCycles; i++) begin
      req_valid = 1'($urandom());
      req_write = 1'($urandom());
      req_addr = AddrWidth'($urandom());
      req_wdata = DataWidth'({$urandom(), $urandom()});
      req_wstrb = StrobeWidth'($urandom());
      req_privileged = 1'($urandom());
      req_secure = 1'($urandom());
      req_abort = 1'b0;
      td.wait_cycles();
      check_response(req_valid, "randomized response");

      if (req_valid) begin
        req_valid = 1'b0;
        req_abort = 1'($urandom());
        td.wait_cycles();
        check_response(1'b0, "idle after randomized response");
        req_abort = 1'b0;
      end
    end

    req_valid = 1'b0;
    req_abort = 1'b0;
    td.wait_cycles();
    check_response(1'b0, "final idle");
    td.finish();
  end

endmodule : br_csr_default_responder_tb
