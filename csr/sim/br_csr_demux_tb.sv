module br_csr_demux_tb;
  parameter int AddrWidth = 4;
  parameter int DataWidth = 32;
  parameter int NumDownstreams = 2;
  parameter int NumRetimeStagesPerDownstream = 0;
  parameter int NumRequests = 100;

  localparam int NumRetimeStages[NumDownstreams] = '{default: NumRetimeStagesPerDownstream};
  localparam int TotalAddressSpace = 1 << (AddrWidth - 1);
  localparam int SizePerDownstream = TotalAddressSpace / NumDownstreams;
  localparam int StrobeWidth = DataWidth / 8;

  logic clk;
  logic rst;

  logic upstream_req_valid;
  logic upstream_req_write;
  logic [AddrWidth-1:0] upstream_req_addr;
  logic [DataWidth-1:0] upstream_req_wdata;
  logic [StrobeWidth-1:0] upstream_req_wstrb;
  logic upstream_req_privileged;
  logic upstream_req_secure;
  logic upstream_req_abort;

  logic upstream_resp_valid;
  logic [DataWidth-1:0] upstream_resp_rdata;
  logic upstream_resp_decerr;
  logic upstream_resp_slverr;

  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_base;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_limit;

  logic [NumDownstreams-1:0] downstream_req_valid;
  logic [NumDownstreams-1:0] downstream_req_write;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr;
  logic [NumDownstreams-1:0][DataWidth-1:0] downstream_req_wdata;
  logic [NumDownstreams-1:0][StrobeWidth-1:0] downstream_req_wstrb;
  logic [NumDownstreams-1:0] downstream_req_privileged;
  logic [NumDownstreams-1:0] downstream_req_secure;
  logic [NumDownstreams-1:0] downstream_req_abort;

  logic [NumDownstreams-1:0] downstream_resp_valid;
  logic [NumDownstreams-1:0][DataWidth-1:0] downstream_resp_rdata;
  logic [NumDownstreams-1:0] downstream_resp_decerr;
  logic [NumDownstreams-1:0] downstream_resp_slverr;



  br_test_driver td (
      .clk,
      .rst
  );

  br_csr_demux #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .NumDownstreams(NumDownstreams),
      .NumRetimeStages(NumRetimeStages)
  ) dut (
      .clk,
      .rst,
      .upstream_req_valid,
      .upstream_req_write,
      .upstream_req_addr,
      .upstream_req_wdata,
      .upstream_req_wstrb,
      .upstream_req_privileged,
      .upstream_req_secure,
      .upstream_req_abort,
      .upstream_resp_valid,
      .upstream_resp_rdata,
      .upstream_resp_decerr,
      .upstream_resp_slverr,
      .downstream_addr_base,
      .downstream_addr_limit,
      .downstream_req_valid,
      .downstream_req_write,
      .downstream_req_addr,
      .downstream_req_wdata,
      .downstream_req_wstrb,
      .downstream_req_privileged,
      .downstream_req_secure,
      .downstream_req_abort,
      .downstream_resp_valid,
      .downstream_resp_rdata,
      .downstream_resp_decerr,
      .downstream_resp_slverr
  );

  task automatic send_and_check_request();
    int expected_dest;
    int expected_req_delay;
    int resp_delay;
    logic expected_req_write;
    logic [AddrWidth-1:0] expected_req_addr;
    logic [DataWidth-1:0] expected_req_wdata;
    logic [StrobeWidth-1:0] expected_req_wstrb;
    logic expected_req_privileged;
    logic expected_req_secure;
    logic [DataWidth-1:0] expected_resp_rdata;
    logic expected_resp_decerr;
    logic expected_resp_slverr;

    upstream_req_valid = 1;
    upstream_req_write = $urandom_range(0, 1);
    upstream_req_addr = $urandom_range(0, TotalAddressSpace - 1);
    upstream_req_wdata = $urandom();
    upstream_req_wstrb = $urandom();
    upstream_req_privileged = $urandom_range(0, 1);
    upstream_req_secure = $urandom_range(0, 1);

    expected_req_write = upstream_req_write;
    expected_req_addr = upstream_req_addr;
    expected_req_wdata = upstream_req_wdata;
    expected_req_wstrb = upstream_req_wstrb;
    expected_req_privileged = upstream_req_privileged;
    expected_req_secure = upstream_req_secure;

    expected_dest = upstream_req_addr / SizePerDownstream;
    expected_req_delay = NumRetimeStages[expected_dest];

    // Make sure the upstream request goes low
    fork
      begin
        @(negedge clk);
        upstream_req_valid = 0;
      end
    join_none

    // Check that we get the downstream request at the expected time
    repeat (expected_req_delay + 1) @(posedge clk);
    td.check(downstream_req_valid[expected_dest], "Downstream request is not valid");
    for (int i = 0; i < NumDownstreams; i++) begin
      if (i != expected_dest) begin
        td.check(!downstream_req_valid[i],
                 "Downstream request is valid for unexpected destination");
      end
    end
    td.check_integer(downstream_req_write[expected_dest], expected_req_write,
                     "Downstream request write mismatch");
    td.check_integer(downstream_req_addr[expected_dest], expected_req_addr,
                     "Downstream request address mismatch");
    td.check_integer(downstream_req_wdata[expected_dest], expected_req_wdata,
                     "Downstream request wdata mismatch");
    td.check_integer(downstream_req_wstrb[expected_dest], expected_req_wstrb,
                     "Downstream request wstrb mismatch");
    td.check_integer(downstream_req_privileged[expected_dest], expected_req_privileged,
                     "Downstream request privileged mismatch");
    td.check_integer(downstream_req_secure[expected_dest], expected_req_secure,
                     "Downstream request secure mismatch");

    // Generate the response
    @(negedge clk);
    resp_delay = $urandom_range(0, 4);
    repeat (resp_delay) @(negedge clk);

    downstream_resp_valid[expected_dest] = 1'b1;
    downstream_resp_rdata[expected_dest] = $urandom();
    downstream_resp_decerr[expected_dest] = $urandom_range(0, 1);
    downstream_resp_slverr[expected_dest] = $urandom_range(0, 1);

    expected_resp_rdata = downstream_resp_rdata[expected_dest];
    expected_resp_decerr = downstream_resp_decerr[expected_dest];
    expected_resp_slverr = downstream_resp_slverr[expected_dest];

    // Make sure the response valid goes low
    fork
      begin
        @(negedge clk);
        downstream_resp_valid[expected_dest]  = 0;
        downstream_resp_rdata[expected_dest]  = 0;
        downstream_resp_decerr[expected_dest] = 0;
        downstream_resp_slverr[expected_dest] = 0;
      end
    join_none

    // Response has same delay as request
    repeat (expected_req_delay + 1) @(posedge clk);

    // Check that we get the upstream response at the expected time
    td.check(upstream_resp_valid, "Upstream response is not valid");
    td.check_integer(upstream_resp_rdata, expected_resp_rdata, "Upstream response rdata mismatch");
    td.check_integer(upstream_resp_decerr, expected_resp_decerr,
                     "Upstream response decerr mismatch");
    td.check_integer(upstream_resp_slverr, expected_resp_slverr,
                     "Upstream response slverr mismatch");

    @(negedge clk);

    // Wait for asynchronous tasks to finish
    wait fork;
  endtask

  task automatic send_and_check_decode_error();
    upstream_req_valid = 1;
    upstream_req_write = 0;
    upstream_req_addr = TotalAddressSpace + 1;
    upstream_req_wdata = 0;
    upstream_req_wstrb = 0;
    upstream_req_privileged = 0;
    upstream_req_secure = 0;

    @(negedge clk);
    upstream_req_valid = 0;

    @(posedge clk);
    td.check(upstream_resp_valid, "Upstream response is not valid");
    td.check_integer(upstream_resp_rdata, 0, "Upstream response rdata mismatch");
    td.check_integer(upstream_resp_decerr, 1, "Upstream response decerr mismatch");
    td.check_integer(upstream_resp_slverr, 0, "Upstream response slverr mismatch");

    @(negedge clk);
  endtask

  initial begin
    for (int i = 0; i < NumDownstreams; i++) begin
      downstream_addr_base[i]  = i * SizePerDownstream;
      downstream_addr_limit[i] = (i + 1) * SizePerDownstream - 1;
    end

    upstream_req_valid = 0;
    upstream_req_write = 0;
    upstream_req_addr = 0;
    upstream_req_wdata = 0;
    upstream_req_wstrb = 0;
    upstream_req_privileged = 0;
    upstream_req_secure = 0;
    upstream_req_abort = 0;

    downstream_resp_valid = 0;
    downstream_resp_rdata = 0;
    downstream_resp_decerr = 0;
    downstream_resp_slverr = 0;

    td.reset_dut();
    td.wait_cycles(2);

    for (int i = 0; i < NumRequests; i++) begin
      $display("Sending request %0d", i);
      send_and_check_request();
    end

    $display("Sending decode error request");
    send_and_check_decode_error();

    td.finish();
  end
endmodule
