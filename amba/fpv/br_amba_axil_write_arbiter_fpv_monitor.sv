// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4-Lite Write Arbiter FPV checks
//
// Design specification:
// - Accept complete AXI4-Lite writes from NumInitiators upstream initiators.
// - Pair each initiator's AW and W channels before admitting the request.
// - Select complete requests with round-robin arbitration and admit at most one per cycle.
// - Preserve accepted request order while allowing downstream AW and W to drain independently.
// - Limit accepted writes to MaxOutstandingWrites until downstream B responses retire ownership.
// - Route each downstream B response to the initiator that owns the oldest outstanding write.
//
// Input assumptions:
// - Installed Cadence AXI4-Lite ABVIP constrains each upstream initiator to legal write-channel
//   behavior, including valid/payload stability and eventual progress under backpressure.
// - Installed Cadence AXI4-Lite ABVIP constrains the downstream target to legal ready/response
//   behavior, including ordered responses and eventual progress.
//
// Testplan for the full monitor:
// - Use write-only AXI4-Lite ABVIP on every upstream initiator and the downstream target for
//   protocol legality, stability, liveness, ordering, and backpressure checks.
// - Check downstream AW and W payload integrity and accepted-request ordering independently.
// - Check outstanding-write capacity, ownership conservation, and backpressure at the limit.
// - Check B-response order, payload integrity, onehot routing, and exact initiator ownership.
// - Cover simultaneous requests, the outstanding limit, and responses to every initiator. ABVIP
//   owns standard channel/backpressure coverage, while instantiated Bedrock blocks own their
//   standalone join, arbitration, fork, buffering, and demux checks.
// - Sweep NumInitiators over 2 and 3 and MaxOutstandingWrites over 1 and 2; retain default widths.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_write_arbiter_fpv_monitor #(
    parameter int NumInitiators = 2,
    parameter int AddrWidth = 40,
    parameter int DataWidth = 64,
    parameter int AWUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int BUserWidth = 1,
    parameter int MaxOutstandingWrites = 1,
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,  // Synchronous, active-high reset

    // AXI4-Lite upstream initiator interfaces
    input logic [NumInitiators-1:0][AddrWidth-1:0] upstream_awaddr,
    input logic [NumInitiators-1:0][br_amba::AxiProtWidth-1:0] upstream_awprot,
    input logic [NumInitiators-1:0][AWUserWidth-1:0] upstream_awuser,
    input logic [NumInitiators-1:0] upstream_awvalid,
    input logic [NumInitiators-1:0] upstream_awready,
    input logic [NumInitiators-1:0][DataWidth-1:0] upstream_wdata,
    input logic [NumInitiators-1:0][StrobeWidth-1:0] upstream_wstrb,
    input logic [NumInitiators-1:0][WUserWidth-1:0] upstream_wuser,
    input logic [NumInitiators-1:0] upstream_wvalid,
    input logic [NumInitiators-1:0] upstream_wready,
    input logic [NumInitiators-1:0][br_amba::AxiRespWidth-1:0] upstream_bresp,
    input logic [NumInitiators-1:0][BUserWidth-1:0] upstream_buser,
    input logic [NumInitiators-1:0] upstream_bvalid,
    input logic [NumInitiators-1:0] upstream_bready,

    // AXI4-Lite downstream target interface
    input logic [AddrWidth-1:0] downstream_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] downstream_awprot,
    input logic [AWUserWidth-1:0] downstream_awuser,
    input logic downstream_awvalid,
    input logic downstream_awready,
    input logic [DataWidth-1:0] downstream_wdata,
    input logic [StrobeWidth-1:0] downstream_wstrb,
    input logic [WUserWidth-1:0] downstream_wuser,
    input logic downstream_wvalid,
    input logic downstream_wready,
    input logic [br_amba::AxiRespWidth-1:0] downstream_bresp,
    input logic [BUserWidth-1:0] downstream_buser,
    input logic downstream_bvalid,
    input logic downstream_bready
);

  localparam int OwnerWidth = $clog2(NumInitiators);
  // Keep ABVIP capacity above the DUT limit so FPV can exercise the DUT's own backpressure.
  localparam int MaxPendingWr = MaxOutstandingWrites + 2;
  localparam int AwPayloadWidth = AddrWidth + br_amba::AxiProtWidth + AWUserWidth;
  localparam int WPayloadWidth = DataWidth + StrobeWidth + WUserWidth;
  localparam int BPayloadWidth = br_amba::AxiRespWidth + BUserWidth;

  logic [NumInitiators-1:0] upstream_aw_handshake;
  logic [NumInitiators-1:0] upstream_w_handshake;
  logic [NumInitiators-1:0] complete_request;
  logic [NumInitiators-1:0] request_accept;
  logic [NumInitiators-1:0][AwPayloadWidth-1:0] fv_aw_incoming_data;
  logic [NumInitiators-1:0][WPayloadWidth-1:0] fv_w_incoming_data;
  logic [NumInitiators-1:0][BPayloadWidth-1:0] fv_upstream_bpayload;
  logic [BPayloadWidth-1:0] fv_downstream_bpayload;
  logic downstream_b_handshake;
  logic [OwnerWidth-1:0] fv_accepted_owner;
  logic [OwnerWidth-1:0] fv_owner;
  logic fv_owner_empty;
  logic fv_owner_full;
  logic [NumInitiators-1:0] fv_expected_bvalid;
  logic fv_expected_downstream_bready;
  logic fv_bpayload_matches;

  assign upstream_aw_handshake = upstream_awvalid & upstream_awready;
  assign upstream_w_handshake = upstream_wvalid & upstream_wready;
  assign complete_request = upstream_awvalid & upstream_wvalid;
  assign request_accept = upstream_aw_handshake & upstream_w_handshake;
  assign downstream_b_handshake = downstream_bvalid & downstream_bready;
  assign fv_downstream_bpayload = {downstream_bresp, downstream_buser};
  assign fv_bpayload_matches = fv_upstream_bpayload[fv_owner] == fv_downstream_bpayload;

  for (genvar i = 0; i < NumInitiators; i++) begin : gen_payload
    assign fv_aw_incoming_data[i]  = {upstream_awaddr[i], upstream_awprot[i], upstream_awuser[i]};
    assign fv_w_incoming_data[i]   = {upstream_wdata[i], upstream_wstrb[i], upstream_wuser[i]};
    assign fv_upstream_bpayload[i] = {upstream_bresp[i], upstream_buser[i]};
  end

  always_comb begin
    fv_accepted_owner = '0;
    for (int i = 0; i < NumInitiators; i++) begin
      if (request_accept[i]) begin
        fv_accepted_owner = OwnerWidth'(i);
      end
    end
  end

  always_comb begin
    fv_expected_bvalid = '0;
    fv_expected_downstream_bready = 1'b0;
    if (!fv_owner_empty) begin
      fv_expected_bvalid[fv_owner]  = downstream_bvalid;
      fv_expected_downstream_bready = upstream_bready[fv_owner];
    end
  end

  // ----------Nonstandard AXI4-Lite USER sideband assumptions----------
  for (genvar i = 0; i < NumInitiators; i++) begin : gen_abvip_gap_assumptions
    // AXI4-Lite ABVIP does not model USER sideband stability on the write address channel.
    `BR_ASSUME(upstream_awuser_stable_a,
               upstream_awvalid[i] && !upstream_awready[i] |=> $stable(upstream_awuser[i]))

    // AXI4-Lite ABVIP does not model USER sideband stability on the write data channel.
    `BR_ASSUME(upstream_wuser_stable_a,
               upstream_wvalid[i] && !upstream_wready[i] |=> $stable(upstream_wuser[i]))
  end

  // AXI4-Lite ABVIP checks BRESP stability but does not model the BUSER sideband.
  `BR_ASSUME(downstream_buser_stable_a, downstream_bvalid && !downstream_bready |=> $stable
                                        (downstream_buser))

  // ----------AXI4-Lite protocol assumptions and checks----------
  // ABVIP drives/constrains the upstream master signals and checks the DUT target signals.
  for (genvar i = 0; i < NumInitiators; i++) begin : gen_upstream_abvip
    axi4_master #(
        .AXI4_LITE(1),
        .ADDR_WIDTH(AddrWidth),
        .DATA_WIDTH(DataWidth),
        .AWUSER_WIDTH(AWUserWidth),
        .WUSER_WIDTH(WUserWidth),
        .BUSER_WIDTH(BUserWidth),
        .MAX_PENDING_WR(MaxPendingWr),
        .MAX_PENDING_RD(0),
        .WRITEONLY_INTERFACE(1),
        .WRITE_RESP_IN_ORDER_ON(1),
        .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
        .CONFIG_WDATA_MASKED(0),
        .ALLOW_SPARSE_STROBE(1),
        .BYTE_STROBE_ON(1)
    ) upstream (
        // Global signals
        .aclk    (clk),
        .aresetn (!rst),
        .csysreq (1'b1),
        .csysack (1'b1),
        .cactive (1'b1),
        // Write Address Channel
        .awvalid (upstream_awvalid[i]),
        .awready (upstream_awready[i]),
        .awuser  (upstream_awuser[i]),
        .awaddr  (upstream_awaddr[i]),
        .awprot  (upstream_awprot[i]),
        .awid    (),
        .awlen   (),
        .awsize  (),
        .awburst (),
        .awlock  (),
        .awcache (),
        .awqos   (),
        .awregion(),
        // Write Data Channel
        .wvalid  (upstream_wvalid[i]),
        .wready  (upstream_wready[i]),
        .wuser   (upstream_wuser[i]),
        .wdata   (upstream_wdata[i]),
        .wstrb   (upstream_wstrb[i]),
        .wlast   (),
        // Write Response Channel
        .bvalid  (upstream_bvalid[i]),
        .bready  (upstream_bready[i]),
        .bresp   (upstream_bresp[i]),
        .buser   (upstream_buser[i]),
        .bid     (),
        // Disabled read channels
        .arvalid (1'b0),
        .arready (1'b0),
        .araddr  ('0),
        .aruser  (),
        .arprot  ('0),
        .arid    (),
        .arlen   (),
        .arsize  (),
        .arburst (),
        .arlock  (),
        .arcache (),
        .arqos   (),
        .arregion(),
        .rvalid  (1'b0),
        .rready  (1'b0),
        .ruser   (),
        .rdata   ('0),
        .rresp   ('0),
        .rid     (),
        .rlast   ()
    );
  end

  // ABVIP drives/constrains the downstream target signals and checks the DUT initiator signals.
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .MAX_PENDING_WR(MaxPendingWr),
      .MAX_PENDING_RD(0),
      .WRITEONLY_INTERFACE(1),
      .WRITE_RESP_IN_ORDER_ON(1),
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) downstream (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (downstream_awvalid),
      .awready (downstream_awready),
      .awuser  (downstream_awuser),
      .awaddr  (downstream_awaddr),
      .awprot  (downstream_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Data Channel
      .wvalid  (downstream_wvalid),
      .wready  (downstream_wready),
      .wuser   (downstream_wuser),
      .wdata   (downstream_wdata),
      .wstrb   (downstream_wstrb),
      .wlast   (),
      // Write Response Channel
      .bvalid  (downstream_bvalid),
      .bready  (downstream_bready),
      .bresp   (downstream_bresp),
      .buser   (downstream_buser),
      .bid     (),
      // Disabled read channels
      .arvalid (1'b0),
      .arready (1'b0),
      .araddr  ('0),
      .aruser  (),
      .arprot  ('0),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      .rvalid  (1'b0),
      .rready  (1'b0),
      .ruser   (),
      .rdata   ('0),
      .rresp   ('0),
      .rid     (),
      .rlast   ()
  );

  // ----------Request ordering and payload integrity----------
  // The AW stream must preserve the arbitration order and payload of accepted requests.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(AwPayloadWidth),
      .IN_CHUNKS(NumInitiators),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingWr)
  ) aw_scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(request_accept),
      .incoming_data(fv_aw_incoming_data),
      .outgoing_vld(downstream_awvalid & downstream_awready),
      .outgoing_data({downstream_awaddr, downstream_awprot, downstream_awuser})
  );

  // The W stream must preserve the arbitration order and payload of accepted requests.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(WPayloadWidth),
      .IN_CHUNKS(NumInitiators),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingWr)
  ) w_scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(request_accept),
      .incoming_data(fv_w_incoming_data),
      .outgoing_vld(downstream_wvalid & downstream_wready),
      .outgoing_data({downstream_wdata, downstream_wstrb, downstream_wuser})
  );

  // Track accepted request owners so B responses can be checked against request order.
  fv_fifo #(
      .Depth(MaxOutstandingWrites),
      .DataWidth(OwnerWidth),
      .Bypass(1)
  ) owner_fifo (
      .clk,
      .rst,
      .push(|request_accept),
      .push_data(fv_accepted_owner),
      .pop(downstream_b_handshake),
      .pop_data(fv_owner),
      .empty(fv_owner_empty),
      .full(fv_owner_full)
  );

  // ----------Composition-specific assertions----------

  // The B-valid vector must select exactly the owner of the oldest accepted request.
  `BR_ASSERT(bvalid_owner_route_a, upstream_bvalid == fv_expected_bvalid)

  // Downstream BREADY must reflect only the oldest owner's readiness.
  `BR_ASSERT(bready_owner_route_a, downstream_bready == fv_expected_downstream_bready)

  // The selected upstream response payload must match the downstream response payload.
  `BR_ASSERT(bpayload_owner_route_a, downstream_bvalid && !fv_owner_empty |-> fv_bpayload_matches)

  // ----------Composition-specific covers----------
  // Exercise simultaneous contention from every initiator.
  `BR_COVER(all_initiators_contend_c, &complete_request)

  // Exercise the configured outstanding-write capacity.
  `BR_COVER(max_outstanding_writes_c, fv_owner_full)

  for (genvar i = 0; i < NumInitiators; i++) begin : gen_response_cover
    // Exercise an accepted response returning to each possible owner.
    `BR_COVER(response_to_initiator_c, upstream_bvalid[i] && upstream_bready[i])
  end

endmodule : br_amba_axil_write_arbiter_fpv_monitor

bind br_amba_axil_write_arbiter br_amba_axil_write_arbiter_fpv_monitor #(
    .NumInitiators(NumInitiators),
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .AWUserWidth(AWUserWidth),
    .WUserWidth(WUserWidth),
    .BUserWidth(BUserWidth),
    .MaxOutstandingWrites(MaxOutstandingWrites)
) monitor (.*);
