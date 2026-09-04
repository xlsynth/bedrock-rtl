// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL Fixed-Priority APB Mux FPV Monitor
//
// Testplan
//
// Design specification:
// - In Setup, lowest-index PSEL wins combinationally and drives the downstream
//   setup phase without an extra arbitration cycle. The winner is saved for an
//   Access of arbitrary duration, then the mux returns to Setup.
// - The current Setup winner or saved Access owner selects live request payload.
// - PRDATA is broadcast. PREADY/PSLVERR reach only the saved Access owner;
//   PSLVERR is not qualified by PREADY and is meaningful at completion.
// - Downstream completion releases ownership even if the winner withdraws its
//   PSEL/PENABLE. This does not guarantee payload stability for malformed input.
//
// Input assumptions and proof boundary:
// - Normal mode uses APB4 protocol VIP. Every requester advances Setup to Access.
//   Protocol hold assumptions use PREADY only to end source-side obligations;
//   they constrain subsequent primary inputs, never the DUT's response values.
// - Recovery mode leaves every upstream and downstream input unconstrained;
//   only the symbolic port index is constrained. No upstream APB VIP or
//   integration assumption may exclude premature PSEL/PENABLE withdrawal.
// - No downstream response fairness or wait-state bound is assumed by safety
//   proofs. Eventual recovery is conditional on eventual downstream PREADY.
// - Startup reset is modeled; repeated live reset is outside this testplan.
// - Fixed priority permits starvation; no all-requester fairness is claimed.
//
// Checks and coverage:
// - Check reset release, setup/access sequencing, arbitrary waits, fixed
//   priority, non-preemption, all payload fields and exact response routing.
// - In normal mode, check APB protocol, request routing and completion
//   correspondence. Cover reads/writes, sparse strobes, errors, waits,
//   contention, every winning port, and consecutive transactions.
// - In recovery mode, prove control/route behavior under arbitrary input and
//   cover PSEL-only/PENABLE-only/both withdrawal through wait, completion,
//   return to Setup and subsequent traffic.
// - Sweep AddrWidth=1,12 and NumUpstreams=1,2,3,4 in both modes.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_apb_mux_fpv_monitor #(
    parameter int AddrWidth = 12,  // Must be at least 1
    parameter int NumUpstreams = 1  // Must be at least 1
) (
    input logic clk,
    input logic rst,

    input logic [NumUpstreams-1:0][AddrWidth-1:0] upstream_paddr,
    input logic [NumUpstreams-1:0] upstream_psel,
    input logic [NumUpstreams-1:0] upstream_penable,
    input logic [NumUpstreams-1:0][br_amba::ApbProtWidth-1:0] upstream_pprot,
    input logic [NumUpstreams-1:0][3:0] upstream_pstrb,
    input logic [NumUpstreams-1:0] upstream_pwrite,
    input logic [NumUpstreams-1:0][31:0] upstream_pwdata,
    input logic [NumUpstreams-1:0][31:0] upstream_prdata,
    input logic [NumUpstreams-1:0] upstream_pready,
    input logic [NumUpstreams-1:0] upstream_pslverr,

    input logic [AddrWidth-1:0] downstream_paddr,
    input logic downstream_psel,
    input logic downstream_penable,
    input logic [br_amba::ApbProtWidth-1:0] downstream_pprot,
    input logic [3:0] downstream_pstrb,
    input logic downstream_pwrite,
    input logic [31:0] downstream_pwdata,
    input logic [31:0] downstream_prdata,
    input logic downstream_pready,
    input logic downstream_pslverr
);

  localparam int UpstreamIdxWidth = NumUpstreams > 1 ? $clog2(NumUpstreams) : 1;

  logic [UpstreamIdxWidth-1:0] magic_u;
  logic higher_priority_pending;
  logic magic_wins;
  logic magic_owner;
  logic magic_selected;
  logic downstream_setup;
  logic downstream_access;
  logic downstream_complete;
  logic magic_complete;
  logic magic_response_enabled;

  if (NumUpstreams > 1) begin : gen_magic_port
    // Quantify over every real port without constraining any DUT input.
    `BR_ASSUME(magic_u_constant_a, $stable(magic_u) && magic_u < NumUpstreams)
  end else begin : gen_single_port
    assign magic_u = '0;
  end

  // Derive the winner independently from the input requests, not the RTL grant.
  always_comb begin
    higher_priority_pending = 1'b0;
    for (int i = 0; i < NumUpstreams; i++) begin
      if (i < int'(magic_u)) higher_priority_pending |= upstream_psel[i];
    end
  end
  assign magic_wins = upstream_psel[magic_u] && !higher_priority_pending;

  // One history bit records whether this arbitrary port won the most recent
  // Setup arbitration. Phase assertions independently check each transition.
  `BR_REGL(magic_owner, magic_wins, !downstream_penable)

  assign downstream_setup = downstream_psel && !downstream_penable;
  assign downstream_access = downstream_psel && downstream_penable;
  assign downstream_complete = downstream_access && downstream_pready;
  assign magic_selected = downstream_setup ? magic_wins : downstream_access && magic_owner;
  assign magic_response_enabled = downstream_access && magic_owner;
  assign magic_complete = upstream_psel[magic_u] && upstream_penable[magic_u] &&
                          upstream_pready[magic_u];

  // Reset releases into Setup, so a current request may launch immediately.
  `BR_ASSERT(reset_release_setup_a, $fell(rst) |-> !downstream_penable)
  // In Setup, current requests drive PSEL combinationally without an idle bubble.
  `BR_ASSERT(no_spurious_setup_a, !downstream_penable && !(|upstream_psel) |-> !downstream_psel)
  `BR_ASSERT(request_drives_setup_a, !downstream_penable && (|upstream_psel) |-> downstream_setup)
  // Setup always advances after one cycle, independently of requester PENABLE.
  `BR_ASSERT(setup_starts_access_a, downstream_setup |=> downstream_access)
  // Downstream backpressure retains the access, even if the requester withdraws.
  `BR_ASSERT(access_holds_until_ready_a,
             downstream_access && !downstream_pready |=> downstream_access)
  // Downstream completion returns to Setup; a pending request may launch immediately.
  `BR_ASSERT(completion_returns_setup_a, downstream_complete |=> !downstream_penable)
  // No access can occur without a selected downstream.
  `BR_ASSERT(enable_requires_select_a, downstream_penable |-> downstream_psel)

  // Check every payload field against the independently identified owner.
  `BR_ASSERT(addr_routing_a, magic_selected |-> downstream_paddr == upstream_paddr[magic_u])
  // Protection attributes follow the selected owner's live request.
  `BR_ASSERT(prot_routing_a, magic_selected |-> downstream_pprot == upstream_pprot[magic_u])
  // Byte strobes follow the selected owner's live request.
  `BR_ASSERT(strb_routing_a, magic_selected |-> downstream_pstrb == upstream_pstrb[magic_u])
  // Read/write direction follows the selected owner's live request.
  `BR_ASSERT(write_routing_a, magic_selected |-> downstream_pwrite == upstream_pwrite[magic_u])
  // Data is a live mux; payload preservation under malformed inputs is not assumed.
  `BR_ASSERT(wdata_routing_a, magic_selected |-> downstream_pwdata == upstream_pwdata[magic_u])
  // Read data is broadcast in all phases, including idle and unselected ports.
  `BR_ASSERT(rdata_broadcast_a, upstream_prdata[magic_u] == downstream_prdata)
  // Only the saved owner receives ready during downstream Access.
  `BR_ASSERT(ready_routing_a,
             upstream_pready[magic_u] == (magic_response_enabled && downstream_pready))
  // Error follows the same ownership mask; the RTL does not qualify it by ready.
  `BR_ASSERT(error_routing_a,
             upstream_pslverr[magic_u] == (magic_response_enabled && downstream_pslverr))
  // A single downstream response cannot acknowledge two upstreams.
  `BR_ASSERT(ready_onehot0_a, $onehot0(upstream_pready))
  // An error cannot be routed to multiple upstreams.
  `BR_ASSERT(error_onehot0_a, $onehot0(upstream_pslverr))

  for (genvar i = 0; i < NumUpstreams; i++) begin : gen_port_covers
    // Each real port can win, including the lowest-priority port.
    `BR_COVER(port_served_c, magic_u == UpstreamIdxWidth'(i) && magic_owner && magic_complete)
  end

  // Exercise zero-wait and delayed transfers with both response outcomes.
  `BR_COVER(zero_wait_c, downstream_setup ##1 downstream_complete)
  `BR_COVER(
      wait_then_complete_c,
      downstream_setup ##1 (downstream_access && !downstream_pready) [* 3] ##1 downstream_complete)
  `BR_COVER(read_complete_c, magic_complete && !upstream_pwrite[magic_u])
  `BR_COVER(write_complete_c, magic_complete && upstream_pwrite[magic_u])
  `BR_COVER(sparse_write_c,
            magic_complete && upstream_pwrite[magic_u] && upstream_pstrb[magic_u] == 4'b0101)
  `BR_COVER(error_complete_c, magic_complete && upstream_pslverr[magic_u])
  `BR_COVER(success_complete_c, magic_complete && !upstream_pslverr[magic_u])
  `BR_COVER(consecutive_transfers_c,
            downstream_complete ##1 downstream_setup ##1 downstream_complete)

  if (NumUpstreams > 1) begin : gen_contention_covers
    // Contention chooses port zero, and the queued last port can be served later.
    `BR_COVER(all_ports_pending_c,
              downstream_setup && (&upstream_psel) && magic_selected && magic_u == 0)
    `BR_COVER(queued_low_priority_served_c,
              downstream_setup && upstream_psel[0] && upstream_psel[NumUpstreams-1]
              ##1 downstream_complete
              ##1 downstream_setup && !upstream_psel[0] && magic_selected &&
                  magic_u == UpstreamIdxWidth'(NumUpstreams-1)
              ##1 magic_complete)
    // A newly arriving higher-priority request cannot preempt the current owner.
    `BR_COVER(higher_priority_arrives_during_wait_c,
              downstream_access && magic_owner && magic_u != 0 && !upstream_psel[0] &&
                  !downstream_pready
              ##1 downstream_access && magic_owner && upstream_psel[0] && !downstream_pready
              ##1 magic_complete)
  end

`ifdef BR_APB_MUX_FPV_RECOVERY
  // No protocol or payload assumptions are applied in this mode. The covers
  // require the same withdrawn requester to wait, complete, return to Setup, and restart.
  // Keep the recovery sequence aligned by sampled cycle.
  // verilog_format: off
  `BR_COVER(drop_select_recovers_c,
            downstream_access && magic_owner && upstream_psel[magic_u] &&
                upstream_penable[magic_u] && !downstream_pready
            ##1 downstream_access && !upstream_psel[magic_u] &&
                upstream_penable[magic_u] && !downstream_pready
            ##1 downstream_complete && !upstream_psel[magic_u] && upstream_penable[magic_u]
            ##1 downstream_setup && magic_wins ##1 magic_complete)
  `BR_COVER(drop_enable_recovers_c,
            downstream_access && magic_owner && upstream_psel[magic_u] &&
                upstream_penable[magic_u] && !downstream_pready
            ##1 downstream_access && upstream_psel[magic_u] &&
                !upstream_penable[magic_u] && !downstream_pready
            ##1 downstream_complete && upstream_psel[magic_u] && !upstream_penable[magic_u]
            ##1 downstream_setup && magic_wins ##1 magic_complete)
  `BR_COVER(drop_both_recovers_c,
            downstream_access && magic_owner && upstream_psel[magic_u] &&
                upstream_penable[magic_u] && !downstream_pready
            ##1 downstream_access && !upstream_psel[magic_u] &&
                !upstream_penable[magic_u] && !downstream_pready
            ##1 downstream_complete && !upstream_psel[magic_u] && !upstream_penable[magic_u]
            ##1 downstream_setup && magic_wins ##1 magic_complete)
  // verilog_format: on
  `BR_COVER(unselected_enable_c, !downstream_psel && upstream_psel == '0 && (|upstream_penable))
  // Demonstrate that no payload-stability assumption leaks into recovery mode.
  `BR_COVER(payload_changes_while_waiting_c,
            downstream_access && magic_owner && !downstream_pready ##1 downstream_access && !$stable
            (downstream_pwdata) && !downstream_pready)
`else
  for (genvar i = 0; i < NumUpstreams; i++) begin : gen_upstream_vip
    apb4_master #(
        .ABUS_WIDTH(AddrWidth)
    ) upstream (
        .pclk(clk),
        .presetn(!rst),
        .psel(upstream_psel[i]),
        .penable(upstream_penable[i]),
        .paddr(upstream_paddr[i]),
        .pwrite(upstream_pwrite[i]),
        .pwdata(upstream_pwdata[i]),
        .pstrb(upstream_pstrb[i]),
        .pprot(upstream_pprot[i]),
        .pready(upstream_pready[i]),
        .prdata(upstream_prdata[i]),
        .pslverr(upstream_pslverr[i])
    );

  end

  apb4_slave #(
      .ABUS_WIDTH(AddrWidth)
  ) downstream (
      .pclk(clk),
      .presetn(!rst),
      .psel(downstream_psel),
      .penable(downstream_penable),
      .paddr(downstream_paddr),
      .pwrite(downstream_pwrite),
      .pwdata(downstream_pwdata),
      .pstrb(downstream_pstrb),
      .pprot(downstream_pprot),
      .pready(downstream_pready),
      .prdata(downstream_prdata),
      .pslverr(downstream_pslverr)
  );

  // Legal requesters retain their Access until the selected downstream completes.
  `BR_ASSERT(
      owner_stays_in_access_a,
      downstream_access && magic_owner |-> upstream_psel[magic_u] && upstream_penable[magic_u])
  // Every downstream completion acknowledges exactly one legal upstream transaction.
  `BR_ASSERT(completion_correspondence_a, downstream_complete == (|upstream_pready))
`endif

endmodule : br_apb_mux_fpv_monitor

bind br_apb_mux br_apb_mux_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .NumUpstreams(NumUpstreams)
) monitor (.*);
