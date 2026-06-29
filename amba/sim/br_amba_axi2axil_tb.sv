// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;
import br_amba_axil_sim_pkg::*;
import br_amba_sim_pkg::*;

// Directed simulation testbench for br_amba_axi2axil.
//
// Scope:
// - checks reset-visible AXI4-Lite request and AXI4 response outputs are idle;
// - converts single-beat, incrementing, fixed, and wrapping AXI bursts into AXI4-Lite accesses;
// - verifies write data passthrough, read data passthrough, response user fields, IDs, and RLAST;
// - checks AXI4 write response propagation returns the first non-OKAY beat response;
// - separates no-stall stress traffic from directed backpressure scenarios;
// - sweeps DataWidth, MaxOutstandingReqs, and NumRandomTransactions from Bazel.
module br_amba_axi2axil_tb;
  parameter int DataWidth = 32;
  parameter int MaxOutstandingReqs = 4;
  parameter int NumRandomTransactions = 1;

  localparam int TimeoutCycles = 100;
  localparam int AddrWidth = 12;
  localparam int IdWidth = 3;
  localparam int AWUserWidth = 2;
  localparam int ARUserWidth = 2;
  localparam int WUserWidth = 2;
  localparam int BUserWidth = 2;
  localparam int RUserWidth = 2;
  localparam int StrobeWidth = DataWidth / 8;
  localparam int AxiSize = $clog2(StrobeWidth);
  localparam int MaxDirectedBeats = 4;
  localparam int NumStressTransactions = 100;
  localparam int NumBackpressureTransactions = MaxOutstandingReqs;
  localparam int MaxBackpressureStallCycles = 3;

  logic clk;
  logic rst;

  // AXI4 manager-side signals.
  logic [AddrWidth-1:0] axi_awaddr;
  logic [IdWidth-1:0] axi_awid;
  logic [AxiBurstLenWidth-1:0] axi_awlen;
  logic [AxiBurstSizeWidth-1:0] axi_awsize;
  logic [AxiBurstTypeWidth-1:0] axi_awburst;
  logic [AxiProtWidth-1:0] axi_awprot;
  logic [AWUserWidth-1:0] axi_awuser;
  logic axi_awvalid;
  logic axi_awready;
  logic [DataWidth-1:0] axi_wdata;
  logic [StrobeWidth-1:0] axi_wstrb;
  logic [WUserWidth-1:0] axi_wuser;
  logic axi_wlast;
  logic axi_wvalid;
  logic axi_wready;
  logic [IdWidth-1:0] axi_bid;
  logic [BUserWidth-1:0] axi_buser;
  logic [AxiRespWidth-1:0] axi_bresp;
  logic axi_bvalid;
  logic axi_bready;
  logic [AddrWidth-1:0] axi_araddr;
  logic [IdWidth-1:0] axi_arid;
  logic [AxiBurstLenWidth-1:0] axi_arlen;
  logic [AxiBurstSizeWidth-1:0] axi_arsize;
  logic [AxiBurstTypeWidth-1:0] axi_arburst;
  logic [AxiProtWidth-1:0] axi_arprot;
  logic [ARUserWidth-1:0] axi_aruser;
  logic axi_arvalid;
  logic axi_arready;
  logic [IdWidth-1:0] axi_rid;
  logic [DataWidth-1:0] axi_rdata;
  logic [RUserWidth-1:0] axi_ruser;
  logic [AxiRespWidth-1:0] axi_rresp;
  logic axi_rlast;
  logic axi_rvalid;
  logic axi_rready;

  // AXI4-Lite target-side signals.
  logic [AddrWidth-1:0] axil_awaddr;
  logic [AxiProtWidth-1:0] axil_awprot;
  logic [AWUserWidth-1:0] axil_awuser;
  logic axil_awvalid;
  logic axil_awready;
  logic [DataWidth-1:0] axil_wdata;
  logic [StrobeWidth-1:0] axil_wstrb;
  logic [WUserWidth-1:0] axil_wuser;
  logic axil_wvalid;
  logic axil_wready;
  logic [AxiRespWidth-1:0] axil_bresp;
  logic [BUserWidth-1:0] axil_buser;
  logic axil_bvalid;
  logic axil_bready;
  logic [AddrWidth-1:0] axil_araddr;
  logic [AxiProtWidth-1:0] axil_arprot;
  logic [ARUserWidth-1:0] axil_aruser;
  logic axil_arvalid;
  logic axil_arready;
  logic [DataWidth-1:0] axil_rdata;
  logic [AxiRespWidth-1:0] axil_rresp;
  logic [RUserWidth-1:0] axil_ruser;
  logic axil_rvalid;
  logic axil_rready;

  logic axi_manager_failed;
  logic axil_target_driver_failed;
  logic axil_request_monitor_failed;
  logic response_monitor_failed;

  br_amba_axi2axil #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(AWUserWidth),
      .ARUserWidth(ARUserWidth),
      .WUserWidth(WUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .MaxOutstandingReqs(MaxOutstandingReqs)
  ) dut (
      .clk(clk),
      .rst(rst),
      .axi_awaddr(axi_awaddr),
      .axi_awid(axi_awid),
      .axi_awlen(axi_awlen),
      .axi_awsize(axi_awsize),
      .axi_awburst(axi_awburst),
      .axi_awprot(axi_awprot),
      .axi_awuser(axi_awuser),
      .axi_awvalid(axi_awvalid),
      .axi_awready(axi_awready),
      .axi_wdata(axi_wdata),
      .axi_wstrb(axi_wstrb),
      .axi_wuser(axi_wuser),
      .axi_wlast(axi_wlast),
      .axi_wvalid(axi_wvalid),
      .axi_wready(axi_wready),
      .axi_bid(axi_bid),
      .axi_buser(axi_buser),
      .axi_bresp(axi_bresp),
      .axi_bvalid(axi_bvalid),
      .axi_bready(axi_bready),
      .axi_araddr(axi_araddr),
      .axi_arid(axi_arid),
      .axi_arlen(axi_arlen),
      .axi_arsize(axi_arsize),
      .axi_arburst(axi_arburst),
      .axi_arprot(axi_arprot),
      .axi_aruser(axi_aruser),
      .axi_arvalid(axi_arvalid),
      .axi_arready(axi_arready),
      .axi_rid(axi_rid),
      .axi_rdata(axi_rdata),
      .axi_ruser(axi_ruser),
      .axi_rresp(axi_rresp),
      .axi_rlast(axi_rlast),
      .axi_rvalid(axi_rvalid),
      .axi_rready(axi_rready),
      .axil_awaddr(axil_awaddr),
      .axil_awprot(axil_awprot),
      .axil_awuser(axil_awuser),
      .axil_awvalid(axil_awvalid),
      .axil_awready(axil_awready),
      .axil_wdata(axil_wdata),
      .axil_wstrb(axil_wstrb),
      .axil_wuser(axil_wuser),
      .axil_wvalid(axil_wvalid),
      .axil_wready(axil_wready),
      .axil_bresp(axil_bresp),
      .axil_buser(axil_buser),
      .axil_bvalid(axil_bvalid),
      .axil_bready(axil_bready),
      .axil_araddr(axil_araddr),
      .axil_arprot(axil_arprot),
      .axil_aruser(axil_aruser),
      .axil_arvalid(axil_arvalid),
      .axil_arready(axil_arready),
      .axil_rdata(axil_rdata),
      .axil_rresp(axil_rresp),
      .axil_ruser(axil_ruser),
      .axil_rvalid(axil_rvalid),
      .axil_rready(axil_rready)
  );

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk(clk),
      .rst(rst)
  );

  br_amba_axi_target_driver #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axi_manager (
      .clk(clk),
      .rst(rst),
      .target_awaddr(axi_awaddr),
      .target_awid(axi_awid),
      .target_awlen(axi_awlen),
      .target_awsize(axi_awsize),
      .target_awburst(axi_awburst),
      .target_awprot(axi_awprot),
      .target_awuser(axi_awuser),
      .target_awvalid(axi_awvalid),
      .target_awready(axi_awready),
      .target_wdata(axi_wdata),
      .target_wstrb(axi_wstrb),
      .target_wuser(axi_wuser),
      .target_wlast(axi_wlast),
      .target_wvalid(axi_wvalid),
      .target_wready(axi_wready),
      .target_bvalid(axi_bvalid),
      .target_bready(axi_bready),
      .target_araddr(axi_araddr),
      .target_arid(axi_arid),
      .target_arlen(axi_arlen),
      .target_arsize(axi_arsize),
      .target_arburst(axi_arburst),
      .target_arprot(axi_arprot),
      .target_aruser(axi_aruser),
      .target_arvalid(axi_arvalid),
      .target_arready(axi_arready),
      .target_rvalid(axi_rvalid),
      .target_rready(axi_rready),
      .failed(axi_manager_failed)
  );

  br_amba_axil_target_driver #(
      .DataWidth(DataWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axil_target (
      .clk(clk),
      .rst(rst),
      .axil_awvalid(axil_awvalid),
      .axil_awready(axil_awready),
      .axil_wvalid(axil_wvalid),
      .axil_wready(axil_wready),
      .axil_bresp(axil_bresp),
      .axil_buser(axil_buser),
      .axil_bvalid(axil_bvalid),
      .axil_bready(axil_bready),
      .axil_arvalid(axil_arvalid),
      .axil_arready(axil_arready),
      .axil_rdata(axil_rdata),
      .axil_rresp(axil_rresp),
      .axil_ruser(axil_ruser),
      .axil_rvalid(axil_rvalid),
      .axil_rready(axil_rready),
      .failed(axil_target_driver_failed)
  );

  br_amba_axil_request_monitor #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axil_request_monitor (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(axil_awaddr),
      .axil_awprot(axil_awprot),
      .axil_awuser(axil_awuser),
      .axil_awvalid(axil_awvalid),
      .axil_awready(axil_awready),
      .axil_wdata(axil_wdata),
      .axil_wstrb(axil_wstrb),
      .axil_wuser(axil_wuser),
      .axil_wvalid(axil_wvalid),
      .axil_wready(axil_wready),
      .axil_araddr(axil_araddr),
      .axil_arprot(axil_arprot),
      .axil_aruser(axil_aruser),
      .axil_arvalid(axil_arvalid),
      .axil_arready(axil_arready),
      .failed(axil_request_monitor_failed)
  );

  br_amba_axi_response_monitor #(
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) response_monitor (
      .clk(clk),
      .rst(rst),
      .axi_bid(axi_bid),
      .axi_buser(axi_buser),
      .axi_bresp(axi_bresp),
      .axi_bvalid(axi_bvalid),
      .axi_bready(axi_bready),
      .axi_rid(axi_rid),
      .axi_rdata(axi_rdata),
      .axi_ruser(axi_ruser),
      .axi_rresp(axi_rresp),
      .axi_rlast(axi_rlast),
      .axi_rvalid(axi_rvalid),
      .axi_rready(axi_rready),
      .failed(response_monitor_failed)
  );

  //----------------------------------------------------------------------------
  // Checks and test helpers
  //----------------------------------------------------------------------------

  task automatic check_reset_outputs();
    td.check(!axil_awvalid, "axil_awvalid asserted after reset");
    td.check(!axil_wvalid, "axil_wvalid asserted after reset");
    td.check(!axi_bvalid, "axi_bvalid asserted after reset");
    td.check(!axil_arvalid, "axil_arvalid asserted after reset");
    td.check(!axi_rvalid, "axi_rvalid asserted after reset");
  endtask

  task automatic check_helpers_passed();
    td.check(!axi_manager_failed, "AXI manager driver reported a failure");
    td.check(!axil_target_driver_failed, "AXI-Lite target driver reported a failure");
    td.check(!axil_request_monitor_failed, "AXI-Lite request monitor reported a failure");
    td.check(!response_monitor_failed, "AXI response monitor reported a failure");
  endtask

  task automatic init_helpers();
    axi_manager.init_idle();
    axil_target.init_idle();
    axil_request_monitor.init_idle();
    response_monitor.init_idle();
  endtask

  task automatic start_test_case();
    init_helpers();
    td.reset_dut();
    td.wait_cycles(2);
    check_reset_outputs();
  endtask

  task automatic finish_test_case();
    check_helpers_passed();
  endtask

  function automatic logic [DataWidth-1:0] get_random_data();
    logic [DataWidth-1:0] random_data;
    logic [31:0] random_word;

    random_data = '0;
    for (int word = 0; word < (DataWidth + 31) / 32; word++) begin
      random_word = $urandom();
      for (int bit_idx = 0; bit_idx < 32; bit_idx++) begin
        if ((word * 32) + bit_idx < DataWidth) begin
          random_data[(word*32)+bit_idx] = random_word[bit_idx];
        end
      end
    end
    get_random_data = random_data;
  endfunction

  function automatic logic [AddrWidth-1:0] get_random_aligned_addr(
      input logic [AxiBurstSizeWidth-1:0] size);
    logic [AddrWidth-1:0] align_mask;

    align_mask = {AddrWidth{1'b1}} << size;
    get_random_aligned_addr = AddrWidth'($urandom()) & align_mask;
  endfunction

  //----------------------------------------------------------------------------
  // Test scenarios
  //----------------------------------------------------------------------------

  task automatic queue_write_burst(
      input axi_aw_t request, input logic [WUserWidth-1:0] wuser,
      input logic [BUserWidth-1:0] buser, input logic [AxiRespWidth-1:0] first_resp,
      input logic [AxiRespWidth-1:0] later_resp, output int unsigned beats);
    logic [AxiRespWidth-1:0] resp;
    logic [ StrobeWidth-1:0] strb;

    beats = int'(request.len) + 1;
    resp  = response_monitor.predict_axi_write_resp(beats, first_resp, later_resp);
    strb  = StrobeWidth'($urandom()) | StrobeWidth'(1'b1);

    for (int unsigned beat = 0; beat < beats; beat++) begin
      logic [AxiRespWidth-1:0] beat_resp;
      logic [AddrWidth-1:0] expected_addr;
      logic [DataWidth-1:0] data;
      logic last;

      data = get_random_data();
      expected_addr = axil_request_monitor.predict_axi2axil_addr(request.addr, request.size,
                                                                 request.len, request.burst, beat);
      last = beat == beats - 1;
      beat_resp = (beat == 0) ? first_resp : later_resp;

      axi_manager.queue_w_beat('{data: AxiDataWidth'(data), strb: AxiStrobeWidth'(strb),
                               user: AxiUserWidth'(wuser), last: last});
      axil_request_monitor.aw_queue.push_back('{addr: AxilAddrWidth'(expected_addr),
                                              prot: request.prot,
                                              user: AxilUserWidth'(request.user)});
      axil_request_monitor.w_queue.push_back('{data: AxilDataWidth'(data),
                                             strb: AxilStrobeWidth'(strb),
                                             user: AxilUserWidth'(wuser)});
      axil_target.queue_b_response('{resp: beat_resp, user: AxilUserWidth'(buser)});
    end
    response_monitor.b_queue.push_back('{id: AxiIdWidth'(request.id), user: AxiUserWidth'(buser),
                                       resp: resp});
  endtask

  task automatic run_write_burst(
      input axi_aw_t request, input logic [WUserWidth-1:0] wuser,
      input logic [BUserWidth-1:0] buser, input logic [AxiRespWidth-1:0] first_resp,
      input logic [AxiRespWidth-1:0] later_resp, input bit stall_outputs);
    int unsigned beats;
    int max_stall_cycles;

    queue_write_burst(request, wuser, buser, first_resp, later_resp, beats);
    max_stall_cycles = stall_outputs ? 2 : 0;

    fork
      axi_manager.run_write_burst(request, max_stall_cycles, stall_outputs ? 2 : 0);
      axil_target.run(beats, 0, max_stall_cycles);
      axil_request_monitor.run(beats, 0);
      response_monitor.run(1, 0);
    join
  endtask

  task automatic queue_read_burst(input axi_ar_t request, input logic [RUserWidth-1:0] ruser,
                                  input logic [AxiRespWidth-1:0] resp, output int unsigned beats);
    beats = int'(request.len) + 1;
    for (int unsigned beat = 0; beat < beats; beat++) begin
      logic [AddrWidth-1:0] expected_addr;
      logic [DataWidth-1:0] data;
      logic last;

      data = get_random_data();
      expected_addr = axil_request_monitor.predict_axi2axil_addr(request.addr, request.size,
                                                                 request.len, request.burst, beat);
      last = beat == beats - 1;

      axil_request_monitor.ar_queue.push_back('{addr: AxilAddrWidth'(expected_addr),
                                              prot: request.prot,
                                              user: AxilUserWidth'(request.user)});
      axil_target.queue_r_response('{data: AxilDataWidth'(data), resp: resp,
                                   user: AxilUserWidth'(ruser)});
      response_monitor.r_queue.push_back('{id: AxiIdWidth'(request.id), data: AxiDataWidth'(data),
                                         resp: resp, user: AxiUserWidth'(ruser), last: last});
    end
  endtask

  task automatic run_read_burst(input axi_ar_t request, input logic [RUserWidth-1:0] ruser,
                                input logic [AxiRespWidth-1:0] resp, input bit stall_outputs);
    int unsigned beats;
    int max_stall_cycles;

    queue_read_burst(request, ruser, resp, beats);
    max_stall_cycles = stall_outputs ? 2 : 0;

    fork
      axi_manager.run_read_burst_fields(AddrWidth'(request.addr), IdWidth'(request.id), request.len,
                                        request.size, request.burst, request.prot,
                                        ARUserWidth'(request.user), max_stall_cycles);
      axil_target.run(0, beats, max_stall_cycles);
      axil_request_monitor.run(0, beats);
      response_monitor.run(0, beats);
    join
  endtask

  task automatic run_parallel_read_write(
      input axi_aw_t write_request, input logic [WUserWidth-1:0] wuser,
      input logic [BUserWidth-1:0] buser, input logic [AxiRespWidth-1:0] first_write_resp,
      input logic [AxiRespWidth-1:0] later_write_resp, input axi_ar_t read_request,
      input logic [RUserWidth-1:0] ruser, input logic [AxiRespWidth-1:0] read_resp,
      input bit stall_outputs);
    int unsigned write_beats;
    int unsigned read_beats;
    int max_stall_cycles;

    queue_write_burst(write_request, wuser, buser, first_write_resp, later_write_resp, write_beats);
    queue_read_burst(read_request, ruser, read_resp, read_beats);
    max_stall_cycles = stall_outputs ? 3 : 0;

    fork
      axi_manager.run_write_burst(write_request, max_stall_cycles, stall_outputs ? 3 : 0);
      axi_manager.run_read_burst_fields(AddrWidth'(read_request.addr), IdWidth'(read_request.id),
                                        read_request.len, read_request.size, read_request.burst,
                                        read_request.prot, ARUserWidth'(read_request.user),
                                        max_stall_cycles);
      axil_target.run(write_beats, read_beats, max_stall_cycles);
      axil_request_monitor.run(write_beats, read_beats);
      response_monitor.run(1, read_beats);
    join
  endtask

  task automatic run_parallel_traffic(
      input int unsigned num_transactions, input int awvalid_max_stall_cycles,
      input int wvalid_max_stall_cycles, input int bready_max_stall_cycles,
      input int arvalid_max_stall_cycles, input int rready_max_stall_cycles,
      input int axil_awready_max_stall_cycles, input int axil_wready_max_stall_cycles,
      input int axil_bvalid_max_stall_cycles, input int axil_arready_max_stall_cycles,
      input int axil_rvalid_max_stall_cycles);
    axi_aw_t write_requests[$];
    axi_ar_t read_requests[$];
    int unsigned total_write_beats;
    int unsigned total_read_beats;

    total_write_beats = 0;
    total_read_beats  = 0;

    for (int unsigned transaction = 0; transaction < num_transactions; transaction++) begin
      axi_aw_t write_request;
      axi_ar_t read_request;
      int unsigned write_beats;
      int unsigned read_beats;

      write_beats = $urandom_range(1, MaxDirectedBeats);
      read_beats = $urandom_range(1, MaxDirectedBeats);

      write_request = '0;
      write_request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
      write_request.id = IdWidth'($urandom());
      write_request.len = AxiBurstLenWidth'(write_beats - 1);
      write_request.size = AxiBurstSizeWidth'(AxiSize);
      write_request.burst = transaction[0] ? AxiBurstFixed : AxiBurstIncr;
      write_request.prot = AxiProtWidth'($urandom());
      write_request.user = AWUserWidth'($urandom());

      read_request = '0;
      read_request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
      read_request.id = IdWidth'($urandom());
      read_request.len = AxiBurstLenWidth'(read_beats - 1);
      read_request.size = AxiBurstSizeWidth'(AxiSize);
      read_request.burst = transaction[0] ? AxiBurstIncr : AxiBurstFixed;
      read_request.prot = AxiProtWidth'($urandom());
      read_request.user = ARUserWidth'($urandom());

      write_requests.push_back(write_request);
      read_requests.push_back(read_request);
      queue_write_burst(write_request, WUserWidth'($urandom()), BUserWidth'($urandom()),
                        AxiRespOkay, transaction[0] ? AxiRespSlverr : AxiRespOkay, write_beats);
      queue_read_burst(read_request, RUserWidth'($urandom()), AxiRespOkay, read_beats);
      total_write_beats += write_beats;
      total_read_beats += read_beats;
    end

    fork
      begin
        while (write_requests.size() > 0) begin
          axi_manager.wait_cycles(get_random_stall_cycles(awvalid_max_stall_cycles));
          axi_manager.drive_aw(write_requests.pop_front());
        end
      end
      begin
        for (int unsigned beat = 0; beat < total_write_beats; beat++) begin
          axi_manager.drive_queued_w(get_random_stall_cycles(wvalid_max_stall_cycles));
        end
      end
      begin
        for (int unsigned response = 0; response < num_transactions; response++) begin
          axi_manager.accept_target_b(get_random_stall_cycles(bready_max_stall_cycles));
        end
      end
      begin
        while (read_requests.size() > 0) begin
          axi_manager.wait_cycles(get_random_stall_cycles(arvalid_max_stall_cycles));
          axi_manager.drive_ar(read_requests.pop_front());
        end
      end
      begin
        for (int unsigned beat = 0; beat < total_read_beats; beat++) begin
          axi_manager.accept_target_r(get_random_stall_cycles(rready_max_stall_cycles));
        end
      end
      axil_target.run(total_write_beats, total_read_beats, 0, axil_awready_max_stall_cycles,
                      axil_wready_max_stall_cycles, axil_bvalid_max_stall_cycles,
                      axil_arready_max_stall_cycles, axil_rvalid_max_stall_cycles);
      axil_request_monitor.run(total_write_beats, total_read_beats);
      response_monitor.run(num_transactions, total_read_beats);
    join
  endtask

  task automatic run_parallel_stress(input int unsigned num_transactions);
    run_parallel_traffic(num_transactions, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
  endtask

  task automatic run_parallel_backpressure(
      input int unsigned num_transactions, input int awvalid_max_stall_cycles,
      input int wvalid_max_stall_cycles, input int bready_max_stall_cycles,
      input int arvalid_max_stall_cycles, input int rready_max_stall_cycles,
      input int axil_awready_max_stall_cycles, input int axil_wready_max_stall_cycles,
      input int axil_bvalid_max_stall_cycles, input int axil_arready_max_stall_cycles,
      input int axil_rvalid_max_stall_cycles);
    run_parallel_traffic(num_transactions, awvalid_max_stall_cycles, wvalid_max_stall_cycles,
                         bready_max_stall_cycles, arvalid_max_stall_cycles, rready_max_stall_cycles,
                         axil_awready_max_stall_cycles, axil_wready_max_stall_cycles,
                         axil_bvalid_max_stall_cycles, axil_arready_max_stall_cycles,
                         axil_rvalid_max_stall_cycles);
  endtask

  task automatic test_single_beat_write();
    axi_aw_t request;

    // Single-beat incrementing burst covers the AXI4 request degenerate case that maps to one
    // AXI-Lite AW/W/B transaction without multi-beat response propagation.
    $display("Checking single-beat write conversion");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = '0;
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstIncr;
    request.prot = AxiProtWidth'($urandom());
    request.user = AWUserWidth'($urandom());
    run_write_burst(request, WUserWidth'($urandom()), BUserWidth'($urandom()), AxiRespOkay,
                    AxiRespOkay, 1'b0);
    finish_test_case();
  endtask

  task automatic test_incr_write_response_propagation();
    axi_aw_t request;

    // Multi-beat incrementing burst checks address stepping, one AXI-Lite write per AXI beat, and
    // propagation of a later SLVERR into the single AXI4 write response.
    $display("Checking incrementing write burst with response propagation");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstIncr;
    request.prot = AxiProtWidth'($urandom());
    request.user = AWUserWidth'($urandom());
    run_write_burst(request, WUserWidth'($urandom()), BUserWidth'($urandom()), AxiRespOkay,
                    AxiRespSlverr, 1'b1);
    finish_test_case();
  endtask

  task automatic test_fixed_write();
    axi_aw_t request;

    // Fixed burst verifies that every generated AXI-Lite write uses the original address, and that
    // the first non-OKAY response wins even when following beats return OKAY.
    $display("Checking fixed write burst");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(3 - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstFixed;
    request.prot = AxiProtWidth'($urandom());
    request.user = AWUserWidth'($urandom());
    run_write_burst(request, WUserWidth'($urandom()), BUserWidth'($urandom()), AxiRespDecerr,
                    AxiRespOkay, 1'b0);
    finish_test_case();
  endtask

  task automatic test_first_write_slverr_response_propagation();
    axi_aw_t request;

    // A first-beat SLVERR must be propagated as the single AXI4 write response, even if the
    // remaining AXI-Lite write beats complete with OKAY.
    $display("Checking first-beat SLVERR write response propagation");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstIncr;
    request.prot = AxiProtWidth'($urandom());
    request.user = AWUserWidth'($urandom());
    run_write_burst(request, WUserWidth'($urandom()), BUserWidth'($urandom()), AxiRespSlverr,
                    AxiRespOkay, 1'b1);
    finish_test_case();
  endtask

  task automatic test_later_write_decerr_response_propagation();
    axi_aw_t request;

    // A later-beat DECERR must be captured after initial OKAY beats and returned on the single
    // AXI4 B response.
    $display("Checking later-beat DECERR write response propagation");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstIncr;
    request.prot = AxiProtWidth'($urandom());
    request.user = AWUserWidth'($urandom());
    run_write_burst(request, WUserWidth'($urandom()), BUserWidth'($urandom()), AxiRespOkay,
                    AxiRespDecerr, 1'b1);
    finish_test_case();
  endtask

  task automatic test_wrapping_read();
    axi_ar_t request;

    // Wrapping read burst validates wrap-boundary address generation while response-side stalls
    // exercise R channel ordering, payload, and RLAST checks.
    $display("Checking wrapping read burst");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstWrap;
    request.prot = AxiProtWidth'($urandom());
    request.user = ARUserWidth'($urandom());
    run_read_burst(request, RUserWidth'($urandom()), AxiRespOkay, 1'b1);
    finish_test_case();
  endtask

  task automatic test_fixed_read();
    axi_ar_t request;

    // Fixed read burst checks repeated AXI-Lite AR addresses and propagation of a non-OKAY read
    // response on every returned AXI4 read beat.
    $display("Checking fixed read burst");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(3 - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstFixed;
    request.prot = AxiProtWidth'($urandom());
    request.user = ARUserWidth'($urandom());
    run_read_burst(request, RUserWidth'($urandom()), AxiRespSlverr, 1'b0);
    finish_test_case();
  endtask

  task automatic test_decerr_read();
    axi_ar_t request;

    // DECERR on the AXI-Lite R channel must propagate unchanged to every AXI4 read beat while
    // preserving the read data, ID, user, and RLAST sequence.
    $display("Checking DECERR read response propagation");
    start_test_case();
    request = '0;
    request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    request.id = IdWidth'($urandom());
    request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    request.size = AxiBurstSizeWidth'(AxiSize);
    request.burst = AxiBurstIncr;
    request.prot = AxiProtWidth'($urandom());
    request.user = ARUserWidth'($urandom());
    run_read_burst(request, RUserWidth'($urandom()), AxiRespDecerr, 1'b1);
    finish_test_case();
  endtask

  task automatic test_parallel_read_write();
    axi_aw_t write_request;
    axi_ar_t read_request;

    // AXI read and write address/data/response channels are independent. This case launches one
    // write burst and one read burst together to check that neither path blocks the other.
    $display("Checking parallel read/write burst conversion");
    start_test_case();
    write_request = '0;
    write_request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    write_request.id = IdWidth'($urandom());
    write_request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    write_request.size = AxiBurstSizeWidth'(AxiSize);
    write_request.burst = AxiBurstIncr;
    write_request.prot = AxiProtWidth'($urandom());
    write_request.user = AWUserWidth'($urandom());

    read_request = '0;
    read_request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
    read_request.id = IdWidth'($urandom());
    read_request.len = AxiBurstLenWidth'(MaxDirectedBeats - 1);
    read_request.size = AxiBurstSizeWidth'(AxiSize);
    read_request.burst = AxiBurstIncr;
    read_request.prot = AxiProtWidth'($urandom());
    read_request.user = ARUserWidth'($urandom());

    run_parallel_read_write(write_request, WUserWidth'($urandom()), BUserWidth'($urandom()),
                            AxiRespOkay, AxiRespOkay, read_request, RUserWidth'($urandom()),
                            AxiRespOkay, 1'b0);
    finish_test_case();
  endtask

  task automatic test_parallel_stress();
    // High-throughput stress keeps all read and write channels active with no intentional stalls.
    // This pushes the interfaces toward one transfer per cycle over many randomized bursts.
    $display("Checking no-stall parallel read/write stress");
    start_test_case();
    run_parallel_stress(NumStressTransactions);
    finish_test_case();
  endtask

  task automatic test_axil_request_backpressure();
    // AXI-Lite target request backpressure independently stalls AWREADY, WREADY, and ARREADY while
    // the AXI manager continues issuing read/write bursts.
    $display("Checking AXI-Lite request-channel backpressure");
    start_test_case();
    run_parallel_backpressure(NumBackpressureTransactions, 0, 0, 0, 0, 0,
                              MaxBackpressureStallCycles, MaxBackpressureStallCycles, 0,
                              MaxBackpressureStallCycles, 0);
    finish_test_case();
  endtask

  task automatic test_axil_response_backpressure();
    // AXI-Lite target response backpressure delays B and R responses after accepting requests,
    // which exercises the bridge response trackers while requests keep flowing.
    $display("Checking AXI-Lite response-channel backpressure");
    start_test_case();
    run_parallel_backpressure(NumBackpressureTransactions, 0, 0, 0, 0, 0, 0, 0,
                              MaxBackpressureStallCycles, 0, MaxBackpressureStallCycles);
    finish_test_case();
  endtask

  task automatic test_axi_response_backpressure();
    // AXI response backpressure stalls BREADY and RREADY. The read side issues the maximum allowed
    // number of outstanding transactions for this parameterization.
    $display("Checking AXI response-channel backpressure");
    start_test_case();
    run_parallel_backpressure(NumBackpressureTransactions, 0, 0, MaxBackpressureStallCycles, 0,
                              MaxBackpressureStallCycles, 0, 0, 0, 0, 0);
    finish_test_case();
  endtask

  task automatic test_axi_source_channel_stalls();
    // Source-side stalls pause AXI AW, W, and AR issuance independently. This complements target
    // backpressure by checking that the bridge accepts the channels whenever they resume.
    $display("Checking AXI source-channel stalls");
    start_test_case();
    run_parallel_backpressure(NumBackpressureTransactions, MaxBackpressureStallCycles,
                              MaxBackpressureStallCycles, 0, MaxBackpressureStallCycles, 0, 0, 0, 0,
                              0, 0);
    finish_test_case();
  endtask

  task automatic test_random_transaction(input int unsigned transaction);
    bit is_write;
    int unsigned beats;

    is_write = $urandom_range(0, 1);
    beats = $urandom_range(1, MaxDirectedBeats);
    start_test_case();
    if (is_write) begin
      axi_aw_t request;

      request = '0;
      request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
      request.id = IdWidth'($urandom());
      request.len = AxiBurstLenWidth'(beats - 1);
      request.size = AxiBurstSizeWidth'(AxiSize);
      request.burst = AxiBurstIncr;
      request.prot = AxiProtWidth'($urandom());
      request.user = AWUserWidth'($urandom());
      run_write_burst(request, WUserWidth'($urandom()), BUserWidth'($urandom()), AxiRespOkay,
                      AxiRespOkay, transaction[0]);
    end else begin
      axi_ar_t request;

      request = '0;
      request.addr = get_random_aligned_addr(AxiBurstSizeWidth'(AxiSize));
      request.id = IdWidth'($urandom());
      request.len = AxiBurstLenWidth'(beats - 1);
      request.size = AxiBurstSizeWidth'(AxiSize);
      request.burst = AxiBurstIncr;
      request.prot = AxiProtWidth'($urandom());
      request.user = ARUserWidth'($urandom());
      run_read_burst(request, RUserWidth'($urandom()), AxiRespOkay, transaction[0]);
    end
    finish_test_case();
  endtask

  task automatic test_random_smoke();
    // Bounded pseudo-random traffic mixes read/write direction, burst length, users, IDs, data, and
    // optional stalls while keeping addresses aligned for legal full-width transfers.
    for (int unsigned transaction = 0; transaction < NumRandomTransactions; transaction++) begin
      test_random_transaction(transaction);
    end
  endtask

  initial begin
    test_single_beat_write();
    test_incr_write_response_propagation();
    test_fixed_write();
    test_first_write_slverr_response_propagation();
    test_later_write_decerr_response_propagation();
    test_wrapping_read();
    test_fixed_read();
    test_decerr_read();
    test_parallel_read_write();
    test_parallel_stress();
    test_axil_request_backpressure();
    test_axil_response_backpressure();
    test_axi_response_backpressure();
    test_axi_source_channel_stalls();
    test_random_smoke();

    td.wait_cycles(10);
    td.finish();
  end

endmodule : br_amba_axi2axil_tb
