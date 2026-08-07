// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4-Lite Write Arbiter
//
// Arbitrates complete AXI4-Lite write requests from multiple upstream initiators onto one
// downstream target. The address and data channels from each initiator are admitted together,
// then buffered independently so the downstream channels can handshake independently. Write
// response ownership is tracked in request order.

`include "br_asserts_internal.svh"

module br_amba_axil_write_arbiter #(
    parameter int NumInitiators = 2,  // Must be at least 2
    parameter int AddrWidth = 40,  // Must be at least 12
    parameter int DataWidth = 64,  // Must be at least 32 and byte aligned
    parameter int AWUserWidth = 1,  // Must be at least 1
    parameter int WUserWidth = 1,  // Must be at least 1
    parameter int BUserWidth = 1,  // Must be at least 1
    parameter int MaxOutstandingWrites = 1,  // Must be at least 1
    localparam int StrobeWidth = DataWidth / 8,
    localparam int OwnerWidth = $clog2(NumInitiators)
) (
    input logic clk,
    input logic rst,  // Synchronous, active-high reset

    // AXI4-Lite upstream initiator interfaces
    input logic [NumInitiators-1:0][AddrWidth-1:0] upstream_awaddr,
    input logic [NumInitiators-1:0][br_amba::AxiProtWidth-1:0] upstream_awprot,
    input logic [NumInitiators-1:0][AWUserWidth-1:0] upstream_awuser,
    input logic [NumInitiators-1:0] upstream_awvalid,
    output logic [NumInitiators-1:0] upstream_awready,
    input logic [NumInitiators-1:0][DataWidth-1:0] upstream_wdata,
    input logic [NumInitiators-1:0][StrobeWidth-1:0] upstream_wstrb,
    input logic [NumInitiators-1:0][WUserWidth-1:0] upstream_wuser,
    input logic [NumInitiators-1:0] upstream_wvalid,
    output logic [NumInitiators-1:0] upstream_wready,
    output logic [NumInitiators-1:0][br_amba::AxiRespWidth-1:0] upstream_bresp,
    output logic [NumInitiators-1:0][BUserWidth-1:0] upstream_buser,
    output logic [NumInitiators-1:0] upstream_bvalid,
    input logic [NumInitiators-1:0] upstream_bready,

    // AXI4-Lite downstream target interface
    output logic [AddrWidth-1:0] downstream_awaddr,
    output logic [br_amba::AxiProtWidth-1:0] downstream_awprot,
    output logic [AWUserWidth-1:0] downstream_awuser,
    output logic downstream_awvalid,
    input logic downstream_awready,
    output logic [DataWidth-1:0] downstream_wdata,
    output logic [StrobeWidth-1:0] downstream_wstrb,
    output logic [WUserWidth-1:0] downstream_wuser,
    output logic downstream_wvalid,
    input logic downstream_wready,
    input logic [br_amba::AxiRespWidth-1:0] downstream_bresp,
    input logic [BUserWidth-1:0] downstream_buser,
    input logic downstream_bvalid,
    output logic downstream_bready
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_initiators_gte_2_a, NumInitiators >= 2)
  `BR_ASSERT_STATIC(addr_width_gte_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_gte_32_a, DataWidth >= 32)
  `BR_ASSERT_STATIC(data_width_byte_aligned_a, DataWidth % 8 == 0)
  `BR_ASSERT_STATIC(aw_user_width_gte_1_a, AWUserWidth >= 1)
  `BR_ASSERT_STATIC(w_user_width_gte_1_a, WUserWidth >= 1)
  `BR_ASSERT_STATIC(b_user_width_gte_1_a, BUserWidth >= 1)
  `BR_ASSERT_STATIC(max_outstanding_writes_gte_1_a, MaxOutstandingWrites >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int NumForks = 3;
  localparam int AwFork = 0;
  localparam int WFork = 1;
  localparam int OwnerFork = 2;
  localparam int AwPayloadWidth = AddrWidth + br_amba::AxiProtWidth + AWUserWidth;
  localparam int WPayloadWidth = DataWidth + StrobeWidth + WUserWidth;
  localparam int BPayloadWidth = br_amba::AxiRespWidth + BUserWidth;

  typedef struct packed {
    logic [AddrWidth-1:0] awaddr;
    logic [br_amba::AxiProtWidth-1:0] awprot;
    logic [AWUserWidth-1:0] awuser;
    logic [DataWidth-1:0] wdata;
    logic [StrobeWidth-1:0] wstrb;
    logic [WUserWidth-1:0] wuser;
    logic [OwnerWidth-1:0] owner;
  } write_request_t;

  typedef struct packed {
    logic [br_amba::AxiRespWidth-1:0] bresp;
    logic [BUserWidth-1:0] buser;
  } write_response_t;

  logic [NumInitiators-1:0] request_push_ready;
  logic [NumInitiators-1:0] request_push_valid;
  write_request_t [NumInitiators-1:0] request_push_data;
  logic request_pop_ready;
  logic request_pop_valid;
  write_request_t request_pop_data;
  logic [NumForks-1:0] request_fork_ready;
  logic [NumForks-1:0] request_fork_valid;
  logic owner_valid;
  logic owner_ready;
  logic [OwnerWidth-1:0] owner;
  logic response_push_ready;
  logic response_push_valid;
  write_response_t [NumInitiators-1:0] upstream_bpayload;

  for (genvar i = 0; i < NumInitiators; i++) begin : gen_request
    localparam logic [OwnerWidth-1:0] Owner = i;

    br_flow_join #(
        .NumFlows(2)
    ) br_flow_join_aw_w (
        .clk,
        .rst,
        .push_ready({upstream_awready[i], upstream_wready[i]}),
        .push_valid({upstream_awvalid[i], upstream_wvalid[i]}),
        .pop_ready (request_push_ready[i]),
        .pop_valid (request_push_valid[i])
    );

    assign request_push_data[i] = '{
            awaddr: upstream_awaddr[i],
            awprot: upstream_awprot[i],
            awuser: upstream_awuser[i],
            wdata: upstream_wdata[i],
            wstrb: upstream_wstrb[i],
            wuser: upstream_wuser[i],
            owner: Owner
        };
  end

  br_flow_mux_rr #(
      .NumFlows(NumInitiators),
      .Width($bits(write_request_t))
  ) br_flow_mux_rr (
      .clk,
      .rst,
      .push_ready(request_push_ready),
      .push_valid(request_push_valid),
      .push_data(request_push_data),
      .pop_ready(request_pop_ready),
      .pop_valid_unstable(request_pop_valid),
      .pop_data_unstable(request_pop_data)
  );

  br_flow_fork #(
      .NumFlows(NumForks),
      // AW/W fork-output backpressure is reachable only with multiple outstanding writes.
      .EnableCoverPushBackpressure(MaxOutstandingWrites > 1),
      // The owner path can legally backpressure the fork.
      .EnableAssertNoPushBackpressure(0)
  ) br_flow_fork (
      .clk,
      .rst,
      .push_ready(request_pop_ready),
      .push_valid(request_pop_valid),
      .pop_ready(request_fork_ready),
      .pop_valid_unstable(request_fork_valid)
  );

  // The mux output is unstable until the fork atomically admits AW, W, and owner, so all three
  // fork sinks intentionally disable push-data-stability assertions.
  br_flow_reg_fwd #(
      .Width(AwPayloadWidth),
      // A second write can reach a stalled AW register only with multiple outstanding writes.
      .EnableCoverPushBackpressure(MaxOutstandingWrites > 1),
      // With one outstanding write, the AW register input cannot be backpressured.
      .EnableAssertNoPushBackpressure(MaxOutstandingWrites == 1),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_aw (
      .clk,
      .rst,
      .push_ready(request_fork_ready[AwFork]),
      .push_valid(request_fork_valid[AwFork]),
      .push_data ({request_pop_data.awaddr, request_pop_data.awprot, request_pop_data.awuser}),
      .pop_ready (downstream_awready),
      .pop_valid (downstream_awvalid),
      .pop_data  ({downstream_awaddr, downstream_awprot, downstream_awuser})
  );

  br_flow_reg_fwd #(
      .Width(WPayloadWidth),
      // A second write can reach a stalled W register only with multiple outstanding writes.
      .EnableCoverPushBackpressure(MaxOutstandingWrites > 1),
      // With one outstanding write, the W register input cannot be backpressured.
      .EnableAssertNoPushBackpressure(MaxOutstandingWrites == 1),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_w (
      .clk,
      .rst,
      .push_ready(request_fork_ready[WFork]),
      .push_valid(request_fork_valid[WFork]),
      .push_data ({request_pop_data.wdata, request_pop_data.wstrb, request_pop_data.wuser}),
      .pop_ready (downstream_wready),
      .pop_valid (downstream_wvalid),
      .pop_data  ({downstream_wdata, downstream_wstrb, downstream_wuser})
  );

  if (MaxOutstandingWrites == 1) begin : gen_owner_reg
    br_flow_reg_fwd #(
        .Width(OwnerWidth),
        .EnableAssertPushDataStability(0)
    ) br_flow_reg_fwd_owner (
        .clk,
        .rst,
        .push_ready(request_fork_ready[OwnerFork]),
        .push_valid(request_fork_valid[OwnerFork]),
        .push_data (request_pop_data.owner),
        .pop_ready (owner_ready),
        .pop_valid (owner_valid),
        .pop_data  (owner)
    );
  end else begin : gen_owner_fifo
    br_fifo_flops #(
        .Depth(MaxOutstandingWrites),
        .Width(OwnerWidth),
        .EnableBypass(0),
        .EnableAssertPushDataStability(0)
    ) br_fifo_flops_owner (
        .clk,
        .rst,
        .push_ready(request_fork_ready[OwnerFork]),
        .push_valid(request_fork_valid[OwnerFork]),
        .push_data(request_pop_data.owner),
        .pop_ready(owner_ready),
        .pop_valid(owner_valid),
        .pop_data(owner),
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        .empty(),
        .empty_next(),
        .items(),
        .items_next()
    );
  end

  br_flow_demux_select_unstable #(
      .NumFlows(NumInitiators),
      .Width(BPayloadWidth)
  ) br_flow_demux_select_unstable_b (
      .clk,
      .rst,
      .select(owner),
      .push_ready(response_push_ready),
      .push_valid(response_push_valid),
      .push_data({downstream_bresp, downstream_buser}),
      .pop_ready(upstream_bready),
      .pop_valid_unstable(upstream_bvalid),
      .pop_data_unstable(upstream_bpayload)
  );

  for (genvar i = 0; i < NumInitiators; i++) begin : gen_response
    assign upstream_bresp[i] = upstream_bpayload[i].bresp;
    assign upstream_buser[i] = upstream_bpayload[i].buser;
  end

  br_flow_join #(
      .NumFlows(2)
  ) br_flow_join_owner_b (
      .clk,
      .rst,
      .push_ready({downstream_bready, owner_ready}),
      .push_valid({downstream_bvalid, owner_valid}),
      .pop_ready (response_push_ready),
      .pop_valid (response_push_valid)
  );

endmodule : br_amba_axil_write_arbiter
