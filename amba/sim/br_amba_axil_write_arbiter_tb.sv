// SPDX-License-Identifier: Apache-2.0


// Directed and permuted simulation coverage for br_amba_axil_write_arbiter.
//
// Checks complete-request admission, round-robin ordering, independent downstream AW/W
// backpressure, outstanding-write limiting, response ownership, and payload integrity.
module br_amba_axil_write_arbiter_tb;

  parameter int AddrWidth = 12;
  parameter int DataWidth = 32;
  parameter int NumInitiators = 3;
  parameter int MaxOutstandingWrites = 1;
  parameter bit UseMinimumUserWidths = 0;

  localparam int AWUserWidth = UseMinimumUserWidths ? 1 : 3;
  localparam int WUserWidth = UseMinimumUserWidths ? 1 : 2;
  localparam int BUserWidth = UseMinimumUserWidths ? 1 : 4;
  localparam int StrobeWidth = DataWidth / 8;
  localparam int OwnerWidth = $clog2(NumInitiators);
  localparam int TimeoutCycles = 100;
  localparam int ChannelSkewCycles = 3;
  localparam int NumPermutedTransactions = 12;

  typedef struct packed {
    logic [AddrWidth-1:0] awaddr;
    logic [br_amba::AxiProtWidth-1:0] awprot;
    logic [AWUserWidth-1:0] awuser;
    logic [DataWidth-1:0] wdata;
    logic [StrobeWidth-1:0] wstrb;
    logic [WUserWidth-1:0] wuser;
    logic [OwnerWidth-1:0] owner;
  } write_request_t;

  logic clk;
  logic rst;

  logic [NumInitiators-1:0][AddrWidth-1:0] upstream_awaddr;
  logic [NumInitiators-1:0][br_amba::AxiProtWidth-1:0] upstream_awprot;
  logic [NumInitiators-1:0][AWUserWidth-1:0] upstream_awuser;
  logic [NumInitiators-1:0] upstream_awvalid;
  logic [NumInitiators-1:0] upstream_awready;
  logic [NumInitiators-1:0][DataWidth-1:0] upstream_wdata;
  logic [NumInitiators-1:0][StrobeWidth-1:0] upstream_wstrb;
  logic [NumInitiators-1:0][WUserWidth-1:0] upstream_wuser;
  logic [NumInitiators-1:0] upstream_wvalid;
  logic [NumInitiators-1:0] upstream_wready;
  logic [NumInitiators-1:0][br_amba::AxiRespWidth-1:0] upstream_bresp;
  logic [NumInitiators-1:0][BUserWidth-1:0] upstream_buser;
  logic [NumInitiators-1:0] upstream_bvalid;
  logic [NumInitiators-1:0] upstream_bready;

  logic [AddrWidth-1:0] downstream_awaddr;
  logic [br_amba::AxiProtWidth-1:0] downstream_awprot;
  logic [AWUserWidth-1:0] downstream_awuser;
  logic downstream_awvalid;
  logic downstream_awready;
  logic [DataWidth-1:0] downstream_wdata;
  logic [StrobeWidth-1:0] downstream_wstrb;
  logic [WUserWidth-1:0] downstream_wuser;
  logic downstream_wvalid;
  logic downstream_wready;
  logic [br_amba::AxiRespWidth-1:0] downstream_bresp;
  logic [BUserWidth-1:0] downstream_buser;
  logic downstream_bvalid;
  logic downstream_bready;

  write_request_t expected_aw_queue[$];
  write_request_t expected_w_queue[$];
  write_request_t expected_b_queue[$];
  int grant_history[$];
  int upstream_request_count;
  int downstream_aw_count;
  int downstream_w_count;
  int response_count;
  logic aw_wait;
  logic w_wait;
  logic [AddrWidth-1:0] held_awaddr;
  logic [br_amba::AxiProtWidth-1:0] held_awprot;
  logic [AWUserWidth-1:0] held_awuser;
  logic [DataWidth-1:0] held_wdata;
  logic [StrobeWidth-1:0] held_wstrb;
  logic [WUserWidth-1:0] held_wuser;

  br_test_driver #(
      .ResetCycles(3)
  ) td (
      .clk,
      .rst
  );

  br_amba_axil_write_arbiter #(
      .NumInitiators(NumInitiators),
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .BUserWidth(BUserWidth),
      .MaxOutstandingWrites(MaxOutstandingWrites)
  ) dut (
      .clk,
      .rst,
      .upstream_awaddr,
      .upstream_awprot,
      .upstream_awuser,
      .upstream_awvalid,
      .upstream_awready,
      .upstream_wdata,
      .upstream_wstrb,
      .upstream_wuser,
      .upstream_wvalid,
      .upstream_wready,
      .upstream_bresp,
      .upstream_buser,
      .upstream_bvalid,
      .upstream_bready,
      .downstream_awaddr,
      .downstream_awprot,
      .downstream_awuser,
      .downstream_awvalid,
      .downstream_awready,
      .downstream_wdata,
      .downstream_wstrb,
      .downstream_wuser,
      .downstream_wvalid,
      .downstream_wready,
      .downstream_bresp,
      .downstream_buser,
      .downstream_bvalid,
      .downstream_bready
  );

  always @(posedge clk) begin : monitor_handshakes
    write_request_t observed_request;
    write_request_t expected_request;
    logic [NumInitiators-1:0] expected_bvalid;
    int owner;

    if (rst) begin
      expected_aw_queue.delete();
      expected_w_queue.delete();
      expected_b_queue.delete();
      grant_history.delete();
      upstream_request_count = 0;
      downstream_aw_count = 0;
      downstream_w_count = 0;
      response_count = 0;
      aw_wait = 1'b0;
      w_wait = 1'b0;
    end else begin
      td.check($onehot0(upstream_awvalid & upstream_awready),
               "More than one upstream AW request was accepted");
      td.check($onehot0(upstream_wvalid & upstream_wready),
               "More than one upstream W request was accepted");

      for (int i = 0; i < NumInitiators; i++) begin
        td.check(
            (upstream_awvalid[i] && upstream_awready[i]) ==
                 (upstream_wvalid[i] && upstream_wready[i]),
            "Upstream AW and W handshakes were not paired");
        if (upstream_awvalid[i] && upstream_awready[i]) begin
          observed_request = '{
              awaddr: upstream_awaddr[i],
              awprot: upstream_awprot[i],
              awuser: upstream_awuser[i],
              wdata: upstream_wdata[i],
              wstrb: upstream_wstrb[i],
              wuser: upstream_wuser[i],
              owner: OwnerWidth'(i)
          };
          expected_aw_queue.push_back(observed_request);
          expected_w_queue.push_back(observed_request);
          expected_b_queue.push_back(observed_request);
          grant_history.push_back(i);
          upstream_request_count++;
        end
      end

      if (aw_wait) begin
        td.check(downstream_awvalid, "Downstream AWVALID fell while backpressured");
        td.check(downstream_awaddr === held_awaddr, "Downstream AWADDR changed while stalled");
        td.check(downstream_awprot === held_awprot, "Downstream AWPROT changed while stalled");
        td.check(downstream_awuser === held_awuser, "Downstream AWUSER changed while stalled");
      end
      aw_wait = downstream_awvalid && !downstream_awready;
      if (aw_wait) begin
        held_awaddr = downstream_awaddr;
        held_awprot = downstream_awprot;
        held_awuser = downstream_awuser;
      end

      if (w_wait) begin
        td.check(downstream_wvalid, "Downstream WVALID fell while backpressured");
        td.check(downstream_wdata === held_wdata, "Downstream WDATA changed while stalled");
        td.check(downstream_wstrb === held_wstrb, "Downstream WSTRB changed while stalled");
        td.check(downstream_wuser === held_wuser, "Downstream WUSER changed while stalled");
      end
      w_wait = downstream_wvalid && !downstream_wready;
      if (w_wait) begin
        held_wdata = downstream_wdata;
        held_wstrb = downstream_wstrb;
        held_wuser = downstream_wuser;
      end

      if (downstream_awvalid && downstream_awready) begin
        td.check(expected_aw_queue.size() > 0, "Unexpected downstream AW handshake");
        if (expected_aw_queue.size() > 0) begin
          expected_request = expected_aw_queue.pop_front();
          td.check(downstream_awaddr === expected_request.awaddr, "Downstream AWADDR mismatch");
          td.check(downstream_awprot === expected_request.awprot, "Downstream AWPROT mismatch");
          td.check(downstream_awuser === expected_request.awuser, "Downstream AWUSER mismatch");
        end
        downstream_aw_count++;
      end

      if (downstream_wvalid && downstream_wready) begin
        td.check(expected_w_queue.size() > 0, "Unexpected downstream W handshake");
        if (expected_w_queue.size() > 0) begin
          expected_request = expected_w_queue.pop_front();
          td.check(downstream_wdata === expected_request.wdata, "Downstream WDATA mismatch");
          td.check(downstream_wstrb === expected_request.wstrb, "Downstream WSTRB mismatch");
          td.check(downstream_wuser === expected_request.wuser, "Downstream WUSER mismatch");
        end
        downstream_w_count++;
      end

      if (downstream_bvalid) begin
        td.check(expected_b_queue.size() > 0, "Unexpected downstream B response");
        if (expected_b_queue.size() > 0) begin
          expected_request = expected_b_queue[0];
          owner = int'(expected_request.owner);
          expected_bvalid = '0;
          expected_bvalid[owner] = 1'b1;
          td.check(upstream_bvalid == expected_bvalid, "Write response routed to wrong owner");
          td.check(upstream_bresp[owner] === downstream_bresp, "Upstream BRESP mismatch");
          td.check(upstream_buser[owner] === downstream_buser, "Upstream BUSER mismatch");
          td.check(downstream_bready == upstream_bready[owner],
                   "Downstream BREADY did not follow the response owner");
        end
      end else begin
        td.check(upstream_bvalid == '0, "Unexpected upstream BVALID without downstream BVALID");
      end

      if (downstream_bvalid && downstream_bready) begin
        if (expected_b_queue.size() > 0) begin
          expected_request = expected_b_queue.pop_front();
        end
        response_count++;
      end
    end
  end

  task automatic set_write_payload(input int initiator, input int transaction_index);
    upstream_awaddr[initiator] = AddrWidth'(16 * (transaction_index + 1) + initiator);
    upstream_awprot[initiator] = br_amba::AxiProtWidth'(transaction_index + initiator);
    upstream_awuser[initiator] = AWUserWidth'(transaction_index + 2 * initiator + 1);
    upstream_wdata[initiator] = DataWidth'(64'h9a5a_c3c3_0123_4567 ^
                                             (transaction_index * 64'h0101_0101_0101_0101) ^
                                             initiator);
    upstream_wuser[initiator] = WUserWidth'(transaction_index + initiator + 1);
    for (int byte_index = 0; byte_index < StrobeWidth; byte_index++) begin
      upstream_wstrb[initiator][byte_index] =
          ((transaction_index + byte_index + initiator) % 2) == 0;
    end
  endtask

  task automatic reset_bus();
    upstream_awaddr = '0;
    upstream_awprot = '0;
    upstream_awuser = '0;
    upstream_awvalid = '0;
    upstream_wdata = '0;
    upstream_wstrb = '0;
    upstream_wuser = '0;
    upstream_wvalid = '0;
    upstream_bready = '0;
    downstream_awready = 1'b0;
    downstream_wready = 1'b0;
    downstream_bresp = '0;
    downstream_buser = '0;
    downstream_bvalid = 1'b0;
    td.reset_dut();
    td.check(!downstream_awvalid, "Downstream AWVALID was set after reset");
    td.check(!downstream_wvalid, "Downstream WVALID was set after reset");
    td.check(upstream_bvalid == '0, "Upstream BVALID was set after reset");
  endtask

  task automatic drive_write(input int initiator, input int transaction_index,
                             input int aw_gap_cycles, input int w_gap_cycles);
    int   aw_timeout;
    int   w_timeout;
    logic aw_handshake;
    logic w_handshake;

    set_write_payload(initiator, transaction_index);
    fork
      begin
        td.wait_cycles(aw_gap_cycles);
        upstream_awvalid[initiator] = 1'b1;
        aw_timeout = TimeoutCycles;
        aw_handshake = 1'b0;
        while (!aw_handshake && aw_timeout > 0) begin
          @(posedge clk);
          aw_handshake = upstream_awvalid[initiator] && upstream_awready[initiator];
          aw_timeout--;
        end
        td.check(aw_handshake, "Timed out waiting for upstream AWREADY");
        @(negedge clk);
        upstream_awvalid[initiator] = 1'b0;
      end
      begin
        td.wait_cycles(w_gap_cycles);
        upstream_wvalid[initiator] = 1'b1;
        w_timeout = TimeoutCycles;
        w_handshake = 1'b0;
        while (!w_handshake && w_timeout > 0) begin
          @(posedge clk);
          w_handshake = upstream_wvalid[initiator] && upstream_wready[initiator];
          w_timeout--;
        end
        td.check(w_handshake, "Timed out waiting for upstream WREADY");
        @(negedge clk);
        upstream_wvalid[initiator] = 1'b0;
      end
    join
  endtask

  task automatic wait_downstream_request(input int request_index);
    int timeout;

    timeout = TimeoutCycles;
    while ((downstream_aw_count <= request_index || downstream_w_count <= request_index) &&
           timeout > 0) begin
      td.wait_cycles();
      timeout--;
    end
    td.check(downstream_aw_count > request_index && downstream_w_count > request_index,
             "Timed out waiting for downstream write request");
  endtask

  task automatic drive_response(input int request_index, input int stall_cycles);
    int   owner;
    int   timeout;
    logic response_handshake;

    wait_downstream_request(request_index);
    td.check(expected_b_queue.size() > 0, "Response-owner queue was empty");
    if (expected_b_queue.size() == 0) begin
      return;
    end

    owner = int'(expected_b_queue[0].owner);
    downstream_bresp = br_amba::AxiRespWidth'(request_index);
    downstream_buser = BUserWidth'(3 * request_index + 1);
    downstream_bvalid = 1'b1;
    upstream_bready = '1;
    upstream_bready[owner] = 1'b0;

    repeat (stall_cycles) begin
      td.wait_cycles();
      td.check(!downstream_bready, "Downstream BREADY ignored owner backpressure");
    end

    upstream_bready[owner] = 1'b1;
    timeout = TimeoutCycles;
    response_handshake = 1'b0;
    while (!response_handshake && timeout > 0) begin
      @(posedge clk);
      response_handshake = downstream_bvalid && downstream_bready;
      timeout--;
    end
    td.check(response_handshake, "Timed out waiting for downstream BREADY");
    @(negedge clk);
    downstream_bvalid = 1'b0;
    downstream_bresp  = '0;
    downstream_buser  = '0;
    upstream_bready   = '0;
  endtask

  task automatic check_drained(input int expected_transactions);
    td.check_integer(upstream_request_count, expected_transactions,
                     "Unexpected number of upstream requests");
    td.check_integer(downstream_aw_count, expected_transactions,
                     "Unexpected number of downstream AW requests");
    td.check_integer(downstream_w_count, expected_transactions,
                     "Unexpected number of downstream W requests");
    td.check_integer(response_count, expected_transactions, "Unexpected number of B responses");
    td.check(expected_aw_queue.size() == 0, "Expected AW queue did not drain");
    td.check(expected_w_queue.size() == 0, "Expected W queue did not drain");
    td.check(expected_b_queue.size() == 0, "Expected B queue did not drain");
  endtask

  task automatic test_upstream_skew(input bit address_first);
    int initiator;

    initiator = address_first ? 0 : NumInitiators - 1;
    reset_bus();
    downstream_awready = 1'b1;
    downstream_wready  = 1'b1;
    set_write_payload(initiator, address_first ? 0 : 1);
    if (address_first) begin
      upstream_awvalid[initiator] = 1'b1;
    end else begin
      upstream_wvalid[initiator] = 1'b1;
    end
    td.wait_cycles(ChannelSkewCycles);
    td.check_integer(upstream_request_count, 0, "Incomplete upstream write was accepted");
    td.check(!downstream_awvalid && !downstream_wvalid,
             "Incomplete upstream write reached the downstream interface");
    if (address_first) begin
      upstream_wvalid[initiator] = 1'b1;
    end else begin
      upstream_awvalid[initiator] = 1'b1;
    end
    td.wait_cycles();
    upstream_awvalid[initiator] = 1'b0;
    upstream_wvalid[initiator]  = 1'b0;
    drive_response(0, 2);
    check_drained(1);
  endtask

  task automatic test_downstream_skew(input bit stall_address);
    int initiator;

    initiator = stall_address ? 0 : NumInitiators - 1;
    reset_bus();
    downstream_awready = !stall_address;
    downstream_wready  = stall_address;
    drive_write(initiator, stall_address ? 2 : 3, 0, 0);
    td.wait_cycles(ChannelSkewCycles);
    if (stall_address) begin
      td.check_integer(downstream_aw_count, 0, "Backpressured AW channel was accepted");
      td.check_integer(downstream_w_count, 1, "Independent W channel did not progress");
      td.check(downstream_awvalid, "Downstream AWVALID was not held during backpressure");
      downstream_awready = 1'b1;
    end else begin
      td.check_integer(downstream_aw_count, 1, "Independent AW channel did not progress");
      td.check_integer(downstream_w_count, 0, "Backpressured W channel was accepted");
      td.check(downstream_wvalid, "Downstream WVALID was not held during backpressure");
      downstream_wready = 1'b1;
    end
    drive_response(0, 2);
    check_drained(1);
  endtask

  task automatic test_complementary_upstream_skew();
    logic [NumInitiators-1:0] accepted;
    int timeout;

    reset_bus();
    downstream_awready = 1'b1;
    downstream_wready  = 1'b1;
    set_write_payload(0, 4);
    set_write_payload(1, 5);
    upstream_awvalid[0] = 1'b1;
    upstream_wvalid[1]  = 1'b1;
    td.wait_cycles(ChannelSkewCycles);
    td.check_integer(upstream_request_count, 0,
                     "Complementary incomplete upstream writes were accepted");
    td.check(!downstream_awvalid && !downstream_wvalid,
             "Complementary incomplete upstream writes reached the downstream interface");

    upstream_wvalid[0]  = 1'b1;
    upstream_awvalid[1] = 1'b1;
    fork
      begin
        accepted = '0;
        timeout  = TimeoutCycles;
        while ((!accepted[0] || !accepted[1]) && timeout > 0) begin
          @(posedge clk);
          for (int i = 0; i < 2; i++) begin
            if (upstream_awvalid[i] && upstream_awready[i]) begin
              accepted[i] = 1'b1;
            end
          end
          @(negedge clk);
          for (int i = 0; i < 2; i++) begin
            upstream_awvalid[i] = !accepted[i];
            upstream_wvalid[i]  = !accepted[i];
          end
          timeout--;
        end
        td.check(accepted[0] && accepted[1], "Timed out waiting for complementary-skew initiators");
      end
      begin
        drive_response(0, 0);
        drive_response(1, 1);
      end
    join
    check_drained(2);
  endtask

  task automatic test_outstanding_limit();
    int   initiator;
    int   timeout;
    logic blocked_handshake;

    reset_bus();
    downstream_awready = 1'b1;
    downstream_wready  = 1'b1;
    for (int i = 0; i < MaxOutstandingWrites; i++) begin
      drive_write(i % NumInitiators, 10 + i, 0, 0);
    end
    wait_downstream_request(MaxOutstandingWrites - 1);

    initiator = MaxOutstandingWrites % NumInitiators;
    set_write_payload(initiator, 10 + MaxOutstandingWrites);
    upstream_awvalid[initiator] = 1'b1;
    upstream_wvalid[initiator]  = 1'b1;
    td.wait_cycles(ChannelSkewCycles);
    td.check_integer(upstream_request_count, MaxOutstandingWrites,
                     "Request was accepted past MaxOutstandingWrites");
    td.check(!upstream_awready[initiator] && !upstream_wready[initiator],
             "Upstream write was ready past MaxOutstandingWrites");

    drive_response(0, 1);
    timeout = TimeoutCycles;
    blocked_handshake = upstream_request_count == MaxOutstandingWrites + 1;
    if (!blocked_handshake) begin
      while (!blocked_handshake && timeout > 0) begin
        @(posedge clk);
        blocked_handshake = upstream_awvalid[initiator] && upstream_awready[initiator];
        timeout--;
      end
      @(negedge clk);
    end
    td.check(blocked_handshake, "Timed out waiting for the blocked upstream request");
    upstream_awvalid[initiator] = 1'b0;
    upstream_wvalid[initiator]  = 1'b0;
    td.check_integer(upstream_request_count, MaxOutstandingWrites + 1,
                     "Blocked request was not accepted after a response");
    for (int i = 1; i <= MaxOutstandingWrites; i++) begin
      drive_response(i, i % 2);
    end
    check_drained(MaxOutstandingWrites + 1);
  endtask

  task automatic drive_contending_requests();
    logic [NumInitiators-1:0] accepted;
    int timeout;

    accepted = '0;
    for (int i = 0; i < NumInitiators; i++) begin
      set_write_payload(i, 30 + i);
    end
    upstream_awvalid = '1;
    upstream_wvalid = '1;
    timeout = TimeoutCycles;
    while (accepted != '1 && timeout > 0) begin
      @(posedge clk);
      for (int i = 0; i < NumInitiators; i++) begin
        if (upstream_awvalid[i] && upstream_awready[i]) begin
          accepted[i] = 1'b1;
        end
      end
      @(negedge clk);
      upstream_awvalid = ~accepted;
      upstream_wvalid  = ~accepted;
      timeout--;
    end
    td.check(accepted == '1, "Timed out waiting for all contending initiators");
  endtask

  task automatic test_round_robin_contention();
    reset_bus();
    downstream_awready = 1'b1;
    downstream_wready  = 1'b1;
    fork
      drive_contending_requests();
      begin
        for (int i = 0; i < NumInitiators; i++) begin
          drive_response(i, i % 2);
        end
      end
    join
    td.check_integer(grant_history.size(), NumInitiators, "Unexpected number of RR grants");
    for (int i = 0; i < NumInitiators; i++) begin
      td.check_integer(grant_history[i], (grant_history[0] + i) % NumInitiators,
                       "Round-robin grant rotation mismatch");
    end
    check_drained(NumInitiators);
  endtask

  task automatic test_permuted_traffic();
    int initiator;

    reset_bus();
    downstream_awready = 1'b1;
    downstream_wready  = 1'b1;
    fork
      begin
        for (int i = 0; i < NumPermutedTransactions; i++) begin
          initiator = NumInitiators - 1 - (i % NumInitiators);
          drive_write(initiator, 50 + i, (i % 3 == 0) ? 2 : 0, (i % 3 == 1) ? 2 : 0);
        end
      end
      begin
        for (int i = 0; i < NumPermutedTransactions; i++) begin
          drive_response(i, i % 3);
        end
      end
    join
    check_drained(NumPermutedTransactions);
  endtask

  initial begin
    test_upstream_skew(1'b1);
    test_upstream_skew(1'b0);
    test_downstream_skew(1'b1);
    test_downstream_skew(1'b0);
    test_complementary_upstream_skew();
    test_outstanding_limit();
    test_round_robin_contention();
    test_permuted_traffic();
    td.finish(10);
  end

endmodule : br_amba_axil_write_arbiter_tb
