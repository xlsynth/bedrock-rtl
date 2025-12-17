// SPDX-License-Identifier: Apache-2.0
//
// Basic unit test for br_csr_axil_widget.

module br_csr_axil_widget_tb;

  parameter int MaxTimeoutCycles = 100;
  parameter int TimeoutCycles = MaxTimeoutCycles;
  parameter int AddrWidth = 16;
  parameter int DataWidth = 32;
  parameter bit RegisterResponseOutputs = 0;
  localparam int StrobeWidth = DataWidth / 8;
  localparam int TimerWidth = br_math::clamped_clog2(MaxTimeoutCycles + 1);

  logic clk;
  logic rst;

  logic axil_awvalid;
  logic axil_awready;
  logic [AddrWidth-1:0] axil_awaddr;
  logic [br_amba::AxiProtWidth-1:0] axil_awprot;
  logic axil_wvalid;
  logic axil_wready;
  logic [DataWidth-1:0] axil_wdata;
  logic [StrobeWidth-1:0] axil_wstrb;
  logic axil_bvalid;
  logic axil_bready;
  logic [br_amba::AxiRespWidth-1:0] axil_bresp;
  logic axil_arvalid;
  logic axil_arready;
  logic [AddrWidth-1:0] axil_araddr;
  logic [br_amba::AxiProtWidth-1:0] axil_arprot;
  logic axil_rvalid;
  logic axil_rready;
  logic [DataWidth-1:0] axil_rdata;
  logic [br_amba::AxiRespWidth-1:0] axil_rresp;

  logic csr_req_valid;
  logic csr_req_write;
  logic [AddrWidth-1:0] csr_req_addr;
  logic [DataWidth-1:0] csr_req_wdata;
  logic [StrobeWidth-1:0] csr_req_wstrb;
  logic csr_req_secure;
  logic csr_req_privileged;
  logic csr_req_abort;

  logic csr_resp_valid;
  logic [DataWidth-1:0] csr_resp_rdata;
  logic csr_resp_slverr;
  logic csr_resp_decerr;

  logic [TimerWidth-1:0] timeout_cycles;
  logic timeout_expired;

  br_csr_axil_widget #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .RegisterResponseOutputs(RegisterResponseOutputs),
      .MaxTimeoutCycles(MaxTimeoutCycles)
  ) dut (
      .clk,
      .rst,
      .axil_awvalid,
      .axil_awready,
      .axil_awaddr,
      .axil_awprot,
      .axil_wvalid,
      .axil_wready,
      .axil_wdata,
      .axil_wstrb,
      .axil_bvalid,
      .axil_bready,
      .axil_bresp,
      .axil_arvalid,
      .axil_arready,
      .axil_araddr,
      .axil_arprot,
      .axil_rvalid,
      .axil_rready,
      .axil_rdata,
      .axil_rresp,
      .csr_req_valid,
      .csr_req_write,
      .csr_req_addr,
      .csr_req_wdata,
      .csr_req_wstrb,
      .csr_req_secure,
      .csr_req_privileged,
      .csr_req_abort,
      .csr_resp_valid,
      .csr_resp_rdata,
      .csr_resp_slverr,
      .csr_resp_decerr,
      .timeout_cycles,
      .timeout_expired
  );

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  task automatic send_axil_write(
      input logic [AddrWidth-1:0] addr, input logic [br_amba::AxiProtWidth-1:0] prot,
      input logic [DataWidth-1:0] wdata, input logic [StrobeWidth-1:0] strb);
    axil_awvalid = 1;
    axil_awaddr  = addr;
    axil_awprot  = prot;
    axil_wvalid  = 1;
    axil_wdata   = wdata;
    axil_wstrb   = strb;

    fork
      begin
        int timeout = 0;
        @(posedge clk);
        while (!axil_awready && timeout < TimeoutCycles) begin
          @(posedge clk);
          timeout++;
        end
        td.check(timeout < TimeoutCycles, "Timeout waiting for AXI-Lite write address ready");
        @(negedge clk);
        axil_awvalid = 0;
      end
      begin
        int timeout = 0;
        @(posedge clk);
        while (!axil_wready && timeout < TimeoutCycles) begin
          @(posedge clk);
          timeout++;
        end
        td.check(timeout < TimeoutCycles, "Timeout waiting for AXI-Lite write data ready");
        @(negedge clk);
        axil_wvalid = 0;
      end
    join

    @(negedge clk);
  endtask

  task automatic send_axil_read(input logic [AddrWidth-1:0] addr,
                                input logic [br_amba::AxiProtWidth-1:0] prot);
    int timeout = 0;

    axil_arvalid = 1;
    axil_araddr  = addr;
    axil_arprot  = prot;

    @(posedge clk);
    while (!axil_arready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for AXI-Lite read address ready");
    @(negedge clk);
    axil_arvalid = 0;
  endtask

  task automatic wait_csr_read(input logic [AddrWidth-1:0] expected_addr,
                               input logic expected_privileged, input logic expected_secure);
    int timeout = 0;

    @(posedge clk);
    while (!csr_req_valid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end

    td.check(timeout < TimeoutCycles, "Timeout waiting for CSR read request");
    td.check(!csr_req_write, "Expected read, not write");
    td.check_integer(csr_req_addr, expected_addr, "CSR request address mismatch");
    td.check_integer(csr_req_privileged, expected_privileged, "CSR request privileged mismatch");
    td.check_integer(csr_req_secure, expected_secure, "CSR request secure mismatch");
    @(negedge clk);
  endtask

  task automatic wait_csr_write(input logic [AddrWidth-1:0] expected_addr,
                                input logic [DataWidth-1:0] expected_wdata,
                                input logic [StrobeWidth-1:0] expected_wstrb,
                                input logic expected_privileged, input logic expected_secure);
    int timeout = 0;
    @(posedge clk);
    while (!csr_req_valid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end

    td.check(timeout < TimeoutCycles, "Timeout waiting for CSR write request");
    td.check(csr_req_write, "Expected write, not read");
    td.check_integer(csr_req_addr, expected_addr, "CSR request address mismatch");
    td.check_integer(csr_req_wdata, expected_wdata, "CSR request wdata mismatch");
    td.check_integer(csr_req_wstrb, expected_wstrb, "CSR request wstrb mismatch");
    td.check_integer(csr_req_privileged, expected_privileged, "CSR request privileged mismatch");
    td.check_integer(csr_req_secure, expected_secure, "CSR request secure mismatch");

    @(negedge clk);
  endtask

  task automatic send_csr_response(input logic [DataWidth-1:0] rdata, input logic slverr,
                                   input logic decerr);
    csr_resp_valid  = 1;
    csr_resp_rdata  = rdata;
    csr_resp_slverr = slverr;
    csr_resp_decerr = decerr;

    @(negedge clk);
    csr_resp_valid  = 0;
    csr_resp_rdata  = 0;
    csr_resp_slverr = 0;
    csr_resp_decerr = 0;
  endtask

  task automatic wait_axil_read_response(input logic [br_amba::AxiRespWidth-1:0] expected_rresp,
                                         input logic [DataWidth-1:0] expected_rdata);
    axil_rready = 1;

    @(posedge clk);
    while (!axil_rvalid) @(posedge clk);

    td.check_integer(axil_rresp, expected_rresp, "AXI-Lite rresp mismatch");
    td.check_integer(axil_rdata, expected_rdata, "AXI-Lite rdata mismatch");

    @(negedge clk);
    axil_rready = 0;
  endtask

  task automatic wait_axil_write_response(input logic [br_amba::AxiRespWidth-1:0] expected_bresp);
    int timeout = 0;
    axil_bready = 1;

    @(posedge clk);
    while (!axil_bvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end

    td.check(timeout < TimeoutCycles, "Timeout waiting for AXI-Lite write response");
    td.check_integer(axil_bresp, expected_bresp, "AXI-Lite bresp mismatch");

    @(negedge clk);
    axil_bready = 0;
  endtask

  initial begin
    axil_awvalid = 0;
    axil_awaddr = 0;
    axil_awprot = 0;
    axil_wvalid = 0;
    axil_wdata = 0;
    axil_wstrb = 0;
    axil_bready = 0;
    axil_arvalid = 0;
    axil_araddr = 0;
    axil_arprot = 0;
    axil_rready = 0;
    csr_resp_valid = 0;
    csr_resp_rdata = 0;
    csr_resp_slverr = 0;
    csr_resp_decerr = 0;
    timeout_cycles = TimeoutCycles;

    td.reset_dut();
    td.wait_cycles(2);

    // Send a write request and check that it's successfully converted
    $display("Checking normal AXI-Lite to CSR write conversion");
    fork
      send_axil_write(16'h0000, 3'b000, 32'h12345678, 4'b1101);
      wait_csr_write(16'h0000, 32'h12345678, 4'b1101, 1'b0, 1'b1);
    join
    fork
      send_csr_response({DataWidth{1'b0}}, 1'b0, 1'b0);
      wait_axil_write_response(br_amba::AxiRespOkay);
    join

    // Send a read request and check that it's successfully converted
    $display("Checking normal AXI-Lite to CSR read conversion");
    fork
      send_axil_read(16'h0010, 3'b000);
      wait_csr_read(16'h0010, 1'b0, 1'b1);
    join
    fork
      send_csr_response(32'hDEADBEEF, 1'b0, 1'b0);
      wait_axil_read_response(br_amba::AxiRespOkay, 32'hDEADBEEF);
    join

    // Send a slverr response for a write request
    $display("Checking AXI-Lite to CSR write conversion with slverr response");
    fork
      send_axil_write(16'h0020, 3'b000, 32'hFFFFFFFF, 4'b0000);
      wait_csr_write(16'h0020, 32'hFFFFFFFF, 4'b0000, 1'b0, 1'b1);
    join
    fork
      send_csr_response(32'hFFFFFFFF, 1'b1, 1'b0);
      wait_axil_write_response(br_amba::AxiRespSlverr);
    join

    // Send a decerr response for a read request
    $display("Checking AXI-Lite to CSR read conversion with decerr response");
    fork
      send_axil_read(16'hFFFF, 3'b000);
      wait_csr_read(16'hFFFF, 1'b0, 1'b1);
    join
    fork
      send_csr_response(32'hFFFFFFFF, 1'b0, 1'b1);
      wait_axil_read_response(br_amba::AxiRespDecerr, 32'hFFFFFFFF);
    join

    // Send read and write requests simultaneously and check the sequencing.
    // Since last request sent was a read, the write should get priority.
    $display("Checking simultaneous read and write requests.");
    fork
      begin
        send_axil_write(16'h0030, 3'b000, 32'hABCD0123, 4'b1111);
        wait_axil_write_response(br_amba::AxiRespOkay);
      end
      begin
        send_axil_read(16'h0040, 3'b000);
        wait_axil_read_response(br_amba::AxiRespOkay, 32'hDEADBEEF);
      end
      begin
        wait_csr_write(16'h0030, 32'hABCD0123, 4'b1111, 1'b0, 1'b1);
        send_csr_response(32'h00000000, 1'b0, 1'b0);
        wait_csr_read(16'h0040, 1'b0, 1'b1);
        send_csr_response(32'hDEADBEEF, 1'b0, 1'b0);
      end
    join

    td.wait_cycles(2);
    td.finish();
  end
endmodule
