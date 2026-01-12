// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL AXI4-Lite to SCB Widget
//
// Converts an AXI4-Lite interface to the Superintelligent CSR Bus (SCB) interface.
//
// The SCB interface is a simple request/response interface that allows only a single
// outstanding request at a time. The conversion of each field from AXI4-Lite is straightforward:
//
// For write requests:
// - csr_req_write <- 1
// - csr_req_addr <- axil_awaddr
// - csr_req_wdata <- axil_wdata
// - csr_req_wstrb <- axil_wstrb
// - csr_req_secure <- !axil_awprot[1]
// - csr_req_privileged <- axil_awprot[0]
// - csr_req_abort <- (special handling, see below)
//
// For read requests:
// - csr_req_write <- 0
// - csr_req_addr <- axil_araddr
// - csr_req_wdata <- 0
// - csr_req_wstrb <- 0
// - csr_req_secure <- !axil_arprot[1]
// - csr_req_privileged <- axil_arprot[0]
//
// The response from the SCB is then converted to the B or R channel
// depending on whether the request was a write or read.
//
// For the R channel:
// - axil_rresp <- 11 if csr_resp_decerr=1, 10 if csr_resp_slverr=1, 00 if neither are set
// - axil_rdata <- csr_resp_rdata
// It is assumed that csr_resp_decerr and csr_resp_slverr cannot both be set for a single response.
//
// For the B channel:
// - axil_bresp <- 11 if csr_resp_decerr=1, 10 if csr_resp_slverr=1, 00 if neither are set
//
// The RegisterResponseOutputs parameter controls whether the response outputs are registered.
//
// The SCB protocol provides a mechanism for the requester to abort an in-progress request after
// a timeout. Compliant SCB peripherals must either guarantee that they will always respond to requests
// in a bounded timeframe or respect the abort signal. The abort mechanism works as follows:
//
// When the SCB request is sent out, a watchdog timer starts counting with a configurable timeout period
// set by the timeout_cycles input.
// When the internal count is greater than or equal to `timeout_cycles`, the watchdog timer will expire.
// When this occurs, the abort signal will be asserted for a single cycle.
// The timer will then reset and count for another timeout period. If no response is received before the
// second period expires, a response with code SLVERR is sent on the appropriate AXI-Lite channel,
// and the request_aborted signal is asserted for a single cycle.
// Changing `timeout_cycles` while a request is active is permitted. If it's changed to a value below the
// current count, the timer will expire immediately.
// Setting `timeout_cycles` to 0 disables the watchdog timer.
//
// SCB leaf nodes that always respond in a bounded timeframe are allowed to
// simply ignore the abort signal. Otherwise, they must handle the abort signal
// properly.  If the inflight request is in a state where completion is not
// guaranteed, the request must be dropped when the abort signal is asserted. It
// must be guaranteed that no response will be sent from then on.

`include "br_asserts_internal.svh"
`include "br_unused.svh"
`include "br_registers.svh"
`include "br_tieoff.svh"

module br_csr_axil_widget #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 32,  // Must be 32 or 64
    parameter bit RegisterResponseOutputs = 0,
    parameter int MaxTimeoutCycles = 1000,  // Must be at least 1

    localparam int StrobeWidth = DataWidth / 8,
    localparam int TimerWidth  = br_math::clamped_clog2(MaxTimeoutCycles + 1)
) (
    input logic clk,
    input logic rst,  // Synchronous, active-high reset

    // AXI4-Lite target interface
    input  logic                             axil_awvalid,
    output logic                             axil_awready,
    input  logic [            AddrWidth-1:0] axil_awaddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input  logic                             axil_wvalid,
    output logic                             axil_wready,
    input  logic [            DataWidth-1:0] axil_wdata,
    input  logic [          StrobeWidth-1:0] axil_wstrb,
    output logic                             axil_bvalid,
    input  logic                             axil_bready,
    output logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input  logic                             axil_arvalid,
    output logic                             axil_arready,
    input  logic [            AddrWidth-1:0] axil_araddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    output logic                             axil_rvalid,
    input  logic                             axil_rready,
    output logic [            DataWidth-1:0] axil_rdata,
    output logic [br_amba::AxiRespWidth-1:0] axil_rresp,

    output logic                   csr_req_valid,
    // 1 indicates a write request, 0 indicates a read request
    output logic                   csr_req_write,
    output logic [  AddrWidth-1:0] csr_req_addr,
    output logic [  DataWidth-1:0] csr_req_wdata,
    output logic [StrobeWidth-1:0] csr_req_wstrb,
    output logic                   csr_req_secure,
    output logic                   csr_req_privileged,
    output logic                   csr_req_abort,

    input logic                 csr_resp_valid,
    input logic [DataWidth-1:0] csr_resp_rdata,
    input logic                 csr_resp_slverr,
    input logic                 csr_resp_decerr,

    input  logic [TimerWidth-1:0] timeout_cycles,
    output logic                  request_aborted
);

  //----------------------------------------------------------------------------
  // Integration checks
  //----------------------------------------------------------------------------
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth == 32 || DataWidth == 64)
  `BR_ASSERT_STATIC(legal_max_timeout_cycles_a, MaxTimeoutCycles >= 1)

  `BR_ASSERT_INTG(legal_timeout_cycles_a, timeout_cycles <= MaxTimeoutCycles)
  `BR_ASSERT_INTG(legal_csr_resp_a, csr_resp_valid |-> !(csr_resp_decerr && csr_resp_slverr))

  //----------------------------------------------------------------------------
  // Implementation
  //----------------------------------------------------------------------------

  logic csr_write_valid;
  logic csr_write_ready;

  br_flow_join #(
      .NumFlows(2)
  ) br_flow_join_csr_write (
      .clk,
      .rst,
      .push_ready({axil_awready, axil_wready}),
      .push_valid({axil_awvalid, axil_wvalid}),
      .pop_ready (csr_write_ready),
      .pop_valid (csr_write_valid)
  );

  typedef struct packed {
    logic [AddrWidth-1:0] addr;
    logic [DataWidth-1:0] wdata;
    logic [StrobeWidth-1:0] wstrb;
    logic write;
    logic secure;
    logic privileged;
  } csr_req_t;

  csr_req_t csr_write_req;
  csr_req_t csr_read_req;
  csr_req_t csr_req;
  logic csr_unqual_req_valid;
  logic csr_unqual_req_ready;

  assign csr_write_req = '{
          addr: axil_awaddr,
          wdata: axil_wdata,
          wstrb: axil_wstrb,
          write: 1'b1,
          secure: !axil_awprot[1],
          privileged: axil_awprot[0]
      };
  assign csr_read_req = '{
          addr: axil_araddr,
          wdata: {DataWidth{1'b0}},
          wstrb: {StrobeWidth{1'b0}},
          write: 1'b0,
          secure: !axil_arprot[1],
          privileged: axil_arprot[0]
      };

  // SCB protocol doesn't distinguish between data and instruction access
  `BR_UNUSED_NAMED(axil_axprot_instr, {axil_awprot[2], axil_arprot[2]})

  br_flow_mux_rr_stable #(
      .NumFlows(2),
      .Width($bits(csr_req_t))
  ) br_flow_mux_rr_stable_csr_req (
      .clk,
      .rst,
      .push_ready({csr_write_ready, axil_arready}),
      .push_valid({csr_write_valid, axil_arvalid}),
      .push_data ({csr_write_req, csr_read_req}),
      .pop_ready (csr_unqual_req_ready),
      .pop_valid (csr_unqual_req_valid),
      .pop_data  (csr_req)
  );

  assign csr_req_valid = csr_unqual_req_valid && csr_unqual_req_ready;
  assign csr_req_addr = csr_req.addr;
  assign csr_req_wdata = csr_req.wdata;
  assign csr_req_wstrb = csr_req.wstrb;
  assign csr_req_write = csr_req.write;
  assign csr_req_secure = csr_req.secure;
  assign csr_req_privileged = csr_req.privileged;

  // Watchdog State Machine
  typedef enum logic [1:0] {
    Idle = 2'b00,
    Active = 2'b01,
    Expired = 2'b10,
    Aborted = 2'b11
  } watchdog_state_t;

  watchdog_state_t wd_state, wd_state_next;
  logic [TimerWidth-1:0] timer_count;
  logic timer_active;
  logic timer_expired;
  logic timer_reset;
  logic timeout_resp_valid;

  assign timer_active = wd_state == Active || wd_state == Expired;
  assign timer_expired = timer_count >= timeout_cycles;
  assign timer_reset = (timer_active && timer_expired) || csr_resp_valid;

  assign timeout_resp_valid = (wd_state == Aborted);
  assign csr_req_abort = (wd_state == Active) && timer_expired;
  assign request_aborted = (wd_state == Expired) && timer_expired && !csr_resp_valid;

  br_counter_incr #(
      .MaxValue(MaxTimeoutCycles)
  ) br_counter_incr_timer (
      .clk,
      .rst,
      .reinit(timer_reset),
      .initial_value('0),
      .incr_valid(timer_active),
      .incr(1'b1),
      .value(timer_count),
      .value_next()
  );

  always_comb begin
    wd_state_next = wd_state;
    // ri lint_check_waive FSM_DEFAULT_REQ
    unique case (wd_state)
      Idle: begin
        if (csr_req_valid) begin
          wd_state_next = Active;
        end
      end
      Active: begin
        if (csr_resp_valid) begin
          wd_state_next = Idle;
        end else if (timer_expired) begin
          wd_state_next = Expired;
        end
      end
      Expired: begin
        if (csr_resp_valid) begin
          wd_state_next = Idle;
        end else if (timer_expired) begin
          wd_state_next = Aborted;
        end
      end
      Aborted: begin
        wd_state_next = Idle;
      end
    endcase
  end

  `BR_REGI(wd_state, wd_state_next, Idle)

  // Only allow one outstanding CSR request at a time
  typedef struct packed {
    br_amba::axi_resp_t   resp;
    logic [DataWidth-1:0] data;
  } resp_t;

  logic inflight, inflight_next;
  logic inflight_write;
  logic merged_resp_valid;
  logic merged_resp_slverr;
  logic merged_resp_decerr;
  logic [DataWidth-1:0] merged_resp_rdata;
  logic buf_resp_valid, buf_resp_valid_next;
  logic buf_resp_ready;
  logic [DataWidth-1:0] buf_resp_rdata;
  logic buf_resp_slverr;
  logic buf_resp_decerr;
  resp_t buf_resp;

  assign merged_resp_valid = csr_resp_valid || timeout_resp_valid;
  assign merged_resp_rdata = timeout_resp_valid ? {DataWidth{1'b0}} : csr_resp_rdata;
  assign merged_resp_slverr = timeout_resp_valid ? 1'b1 : csr_resp_slverr;
  assign merged_resp_decerr = timeout_resp_valid ? 1'b0 : csr_resp_decerr;

  // Set inflight when request is sent out
  // Clear it when the response is accepted
  assign inflight_next = (inflight || csr_req_valid) && !(buf_resp_valid && buf_resp_ready);
  // Set buf_resp_valid when response is received from downstream
  // Clear it when the response is accepted
  assign buf_resp_valid_next = (buf_resp_valid && !buf_resp_ready) || merged_resp_valid;

  `BR_REG(inflight, inflight_next)
  `BR_REGL(inflight_write, csr_req_write, csr_req_valid)
  `BR_REG(buf_resp_valid, buf_resp_valid_next)
  `BR_REGLN(buf_resp_rdata, merged_resp_rdata, merged_resp_valid)
  `BR_REGLN(buf_resp_slverr, merged_resp_slverr, merged_resp_valid)
  `BR_REGLN(buf_resp_decerr, merged_resp_decerr, merged_resp_valid)

  assign csr_unqual_req_ready = !inflight;
  assign buf_resp.data = buf_resp_rdata;
  assign buf_resp.resp =
      buf_resp_decerr ? br_amba::AxiRespDecerr :
      buf_resp_slverr ? br_amba::AxiRespSlverr :
      br_amba::AxiRespOkay;

  logic  axil_bvalid_int;
  logic  axil_bready_int;
  resp_t axil_b_int;

  logic  axil_rvalid_int;
  logic  axil_rready_int;
  resp_t axil_r_int;


  br_flow_demux_select_unstable #(
      .NumFlows(2),
      .Width(br_amba::AxiRespWidth + DataWidth)
  ) br_flow_demux_select_unstable_resp (
      .clk,
      .rst,
      .select(inflight_write),
      .push_ready(buf_resp_ready),
      .push_valid(buf_resp_valid),
      .push_data(buf_resp),
      .pop_ready({axil_bready_int, axil_rready_int}),
      .pop_valid_unstable({axil_bvalid_int, axil_rvalid_int}),
      .pop_data_unstable({axil_b_int, axil_r_int})
  );

  `BR_UNUSED_NAMED(axil_b_int_data, axil_b_int.data)

  if (RegisterResponseOutputs) begin : gen_reg_resp_out
    br_flow_reg_fwd #(
        .Width(br_amba::AxiRespWidth)
    ) br_flow_reg_fwd_b (
        .clk,
        .rst,
        .push_ready(axil_bready_int),
        .push_valid(axil_bvalid_int),
        .push_data ({axil_b_int.resp}),
        .pop_ready (axil_bready),
        .pop_valid (axil_bvalid),
        .pop_data  (axil_bresp)
    );

    br_flow_reg_fwd #(
        .Width(DataWidth + br_amba::AxiRespWidth)
    ) br_flow_reg_fwd_r (
        .clk,
        .rst,
        .push_ready(axil_rready_int),
        .push_valid(axil_rvalid_int),
        .push_data ({axil_r_int.data, axil_r_int.resp}),
        .pop_ready (axil_rready),
        .pop_valid (axil_rvalid),
        .pop_data  ({axil_rdata, axil_rresp})
    );
  end else begin : gen_no_reg_resp_out
    assign axil_bvalid = axil_bvalid_int;
    assign axil_bready_int = axil_bready;
    assign axil_bresp = {axil_b_int.resp};
    assign axil_rvalid = axil_rvalid_int;
    assign axil_rready_int = axil_rready;
    assign axil_rresp = {axil_r_int.resp};
    assign axil_rdata = axil_r_int.data;
  end

  // Implementation assertions
  `BR_ASSERT_IMPL(only_single_request_inflight_a, inflight |-> !csr_req_valid)
  `BR_ASSERT_IMPL(no_spurious_resp_a, csr_resp_valid |-> inflight && !buf_resp_valid)
  `BR_ASSERT_IMPL(timer_resets_after_response_or_timeout_a,
                  timer_active && (csr_resp_valid || timer_expired) |-> timer_reset)

endmodule
