// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL Address-Decoding APB Demux FPV Monitor
//
// Testplan
//
// Design specification:
// - Decode the masked upstream APB address against configurable, non-overlapping
//   downstream address ranges. A zero-sized range is disabled.
// - Route misses to the final downstream when HasDefaultDownstream is set;
//   otherwise complete the transfer locally with zero PRDATA and PSLVERR.
// - Forward the complete APB request to the decoded downstream while applying
//   optional address normalization and the selected downstream address mask.
// - Delegate APB routing, retiming, and response behavior to the separately
//   verified br_apb_demux_select_onehot block.
//
// Input assumptions:
// - The upstream interface follows the APB4 manager protocol. PWDATA also
//   remains stable for pending reads because the RTL checks the full request.
// - Address ranges are legal and non-overlapping when a transfer is active and
//   the address-map inputs remain stable until that transfer completes.
// - Every downstream response interface follows the APB4 subordinate protocol.
//
// Checks:
// - Apply APB4 protocol VIP to the upstream and every downstream interface.
// - For an arbitrary downstream, prove the decoded request reaches only that
//   route with all request fields preserved and PADDR translated as configured.
// - Prove a no-default decode miss activates no downstream and returns PSLVERR.
// - Cover explicit routes, the default route, decode misses, and translated
//   addresses. Wrapper tests use no retiming because retimed transport is
//   already covered by the br_apb_demux_select_onehot environment.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_apb_demux_fpv_monitor #(
    parameter int AddrWidth = 12,
    parameter int NumDownstreams = 1,
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
    parameter bit HasDefaultDownstream = 0,
    localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams,
    parameter bit RequirePowerOfTwoAlignedRanges[NumAddressRanges] = '{default: 1},
    parameter bit NormalizeDownstreamAddress[NumAddressRanges] = '{default: 0},
    parameter logic [AddrWidth-1:0] UpstreamAddrMask = '1,
    parameter logic [NumDownstreams-1:0][AddrWidth-1:0] DownstreamAddrMask = '1
) (
    input logic clk,
    input logic rst,

    input logic [AddrWidth-1:0] upstream_paddr,
    input logic upstream_psel,
    input logic upstream_penable,
    input logic [br_amba::ApbProtWidth-1:0] upstream_pprot,
    input logic [3:0] upstream_pstrb,
    input logic upstream_pwrite,
    input logic [31:0] upstream_pwdata,
    input logic [31:0] upstream_prdata,
    input logic upstream_pready,
    input logic upstream_pslverr,

    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_size,

    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_paddr,
    input logic [NumDownstreams-1:0] downstream_psel,
    input logic [NumDownstreams-1:0] downstream_penable,
    input logic [NumDownstreams-1:0][br_amba::ApbProtWidth-1:0] downstream_pprot,
    input logic [NumDownstreams-1:0][3:0] downstream_pstrb,
    input logic [NumDownstreams-1:0] downstream_pwrite,
    input logic [NumDownstreams-1:0][31:0] downstream_pwdata,
    input logic [NumDownstreams-1:0][31:0] downstream_prdata,
    input logic [NumDownstreams-1:0] downstream_pready,
    input logic [NumDownstreams-1:0] downstream_pslverr
);

  typedef struct packed {
    logic [AddrWidth-1:0] paddr;
    logic [br_amba::ApbProtWidth-1:0] pprot;
    logic [3:0] pstrb;
    logic pwrite;
    logic [31:0] pwdata;
  } req_payload_t;

  localparam int ReqPayloadWidth = $bits(req_payload_t);
  localparam int DownstreamWidth = NumDownstreams == 1 ? 1 : $clog2(NumDownstreams);

  logic [DownstreamWidth-1:0] magic_d;
  logic [AddrWidth-1:0] upstream_paddr_masked;
  logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_limit;
  logic [NumAddressRanges-1:0] downstream_addr_range_disabled;
  logic upstream_addr_hit;
  logic addr_match_magic_d;
  logic magic_d_is_default;
  logic route_magic_d;
  logic decode_miss;
  logic decode_miss_response_ok;
  logic explicit_route_match;
  logic upstream_request_pending;
  logic upstream_req_start;
  logic downstream_req_start;
  logic [AddrWidth-1:0] expected_downstream_paddr;
  req_payload_t expected_req_payload;
  req_payload_t downstream_req_payload;

  assign upstream_paddr_masked = upstream_paddr & UpstreamAddrMask;
  assign upstream_request_pending = upstream_psel && (!upstream_penable || !upstream_pready);
  assign upstream_req_start = upstream_psel && !upstream_penable;
  assign downstream_req_start = downstream_psel[magic_d] && !downstream_penable[magic_d];

  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_addr_range
    assign downstream_addr_limit[i] = downstream_addr_base[i] + downstream_addr_size[i] - 1'b1;
    assign downstream_addr_range_disabled[i] = downstream_addr_size[i] == '0;
  end

  always_comb begin
    upstream_addr_hit = 1'b0;
    addr_match_magic_d = 1'b0;
    expected_downstream_paddr = upstream_paddr;
    for (int i = 0; i < NumAddressRanges; i++) begin
      if (!downstream_addr_range_disabled[i] &&
          upstream_paddr_masked >= downstream_addr_base[i] &&
          upstream_paddr_masked <= downstream_addr_limit[i]) begin
        upstream_addr_hit = 1'b1;
        if (magic_d == DownstreamWidth'(i)) begin
          addr_match_magic_d = 1'b1;
        end
      end
      if (magic_d == DownstreamWidth'(i) && NormalizeDownstreamAddress[i]) begin
        expected_downstream_paddr = upstream_paddr - downstream_addr_base[i];
      end
    end
    expected_downstream_paddr &= DownstreamAddrMask[magic_d];
  end

  assign magic_d_is_default = HasDefaultDownstream && magic_d == DownstreamWidth'(NumAddressRanges);
  assign route_magic_d = addr_match_magic_d || (magic_d_is_default && !upstream_addr_hit);
  assign decode_miss = upstream_psel && !upstream_addr_hit && !HasDefaultDownstream;
  assign decode_miss_response_ok = upstream_pready && upstream_pslverr && upstream_prdata == '0;
  assign explicit_route_match = downstream_req_start && addr_match_magic_d &&
                                downstream_paddr[magic_d] == expected_downstream_paddr;

  assign expected_req_payload = '{
          paddr: expected_downstream_paddr,
          pprot: upstream_pprot,
          pstrb: upstream_pstrb,
          pwrite: upstream_pwrite,
          pwdata: upstream_pwdata
      };
  assign downstream_req_payload = '{
          paddr: downstream_paddr[magic_d],
          pprot: downstream_pprot[magic_d],
          pstrb: downstream_pstrb[magic_d],
          pwrite: downstream_pwrite[magic_d],
          pwdata: downstream_pwdata[magic_d]
      };
  // Pick one arbitrary downstream so a single checker proves every route.
  `BR_ASSUME(magic_d_constant_a, $stable(magic_d) && magic_d < NumDownstreams)

  // Address-map inputs are an integration contract and cannot change mid-transfer.
  `BR_ASSUME(addr_map_stable_while_pending_a, upstream_request_pending |=> $stable
                                              ({downstream_addr_base, downstream_addr_size}))

  // Cover the read-PWDATA stability gap left by APB VIP's write-only PWDATA checks.
  `BR_ASSUME(
      upstream_read_pwdata_stable_a,
      upstream_psel && (!upstream_penable || !upstream_pready) && !upstream_pwrite |=> $stable
      (upstream_pwdata))

  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_addr_assumptions
    // Enabled ranges cannot wrap around the address space.
    `BR_ASSUME(legal_addr_range_a,
               upstream_psel |-> downstream_addr_range_disabled[i] ||
                   downstream_addr_limit[i] >= downstream_addr_base[i])

    if (RequirePowerOfTwoAlignedRanges[i]) begin : gen_power_of_two_range_assumptions
      // Enabled constrained ranges have a power-of-two size.
      `BR_ASSUME(addr_size_power_of_two_a, upstream_psel |-> $onehot0(downstream_addr_size[i]))

      // Enabled constrained ranges begin on their natural alignment.
      `BR_ASSUME(addr_base_aligned_a,
                 upstream_psel |-> downstream_addr_range_disabled[i] ||
                     (downstream_addr_base[i] & (downstream_addr_size[i] - 1'b1)) == '0)

      // The downstream mask preserves every possible in-range address offset.
      `BR_ASSUME(addr_mask_preserves_offsets_a,
                 upstream_psel |-> downstream_addr_range_disabled[i] ||
                     ((downstream_addr_size[i] - 1'b1) & ~DownstreamAddrMask[i]) == '0)
    end
  end

  for (genvar i = 0; i < NumAddressRanges - 1; i++) begin : gen_range_i
    for (genvar j = i + 1; j < NumAddressRanges; j++) begin : gen_range_j
      // Explicit enabled address ranges cannot overlap.
      `BR_ASSUME(no_overlapping_addr_a,
                 upstream_psel |-> downstream_addr_range_disabled[i] ||
                     downstream_addr_range_disabled[j] ||
                     downstream_addr_limit[i] < downstream_addr_base[j] ||
                     downstream_addr_base[i] > downstream_addr_limit[j])
    end
  end

  // Check legality and backpressure behavior of the upstream APB manager traffic.
  apb4_master #(
      .ABUS_WIDTH(AddrWidth)
  ) upstream (
      .pclk(clk),
      .presetn(!rst),
      .psel(upstream_psel),
      .penable(upstream_penable),
      .paddr(upstream_paddr),
      .pwrite(upstream_pwrite),
      .pwdata(upstream_pwdata),
      .pstrb(upstream_pstrb),
      .pprot(upstream_pprot),
      .pready(upstream_pready),
      .prdata(upstream_prdata),
      .pslverr(upstream_pslverr)
  );

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_vip
    // Check each DUT-generated downstream APB request and subordinate response.
    apb4_slave #(
        .ABUS_WIDTH(AddrWidth)
    ) downstream (
        .pclk(clk),
        .presetn(!rst),
        .psel(downstream_psel[i]),
        .penable(downstream_penable[i]),
        .paddr(downstream_paddr[i]),
        .pwrite(downstream_pwrite[i]),
        .pwdata(downstream_pwdata[i]),
        .pstrb(downstream_pstrb[i]),
        .pprot(downstream_pprot[i]),
        .pready(downstream_pready[i]),
        .prdata(downstream_prdata[i]),
        .pslverr(downstream_pslverr[i])
    );
  end

  // Match each decoded request to the selected port and translated payload.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ReqPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(1)
  ) req_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(upstream_req_start && route_magic_d),
      .incoming_data(expected_req_payload),
      .outgoing_vld(downstream_req_start),
      .outgoing_data(downstream_req_payload)
  );

  // The composed decoder and APB router can activate at most one downstream.
  `BR_ASSERT(downstream_select_onehot0_a, $onehot0(downstream_psel))

  // A downstream request can only appear when its address route was selected.
  `BR_ASSERT(no_spurious_decoded_request_a, downstream_req_start |-> route_magic_d)

  if (!HasDefaultDownstream) begin : gen_decode_miss_assertions
    // A no-default decode miss cannot activate any downstream interface.
    `BR_ASSERT(decode_miss_no_downstream_a, decode_miss |-> downstream_psel == '0)

    // A no-default decode miss completes locally with the specified APB error
    // response.
    `BR_ASSERT(decode_miss_response_a, decode_miss && upstream_penable |-> decode_miss_response_ok)
  end

  // Every request decoded to the arbitrary route reaches its finite retiming path.
  `BR_ASSERT(decoded_request_progress_a,
             upstream_req_start && route_magic_d |-> s_eventually downstream_req_start)

  // Exercise an explicit address-range route and its translated output
  // address.
  `BR_COVER(explicit_route_c, explicit_route_match)

  if (HasDefaultDownstream) begin : gen_default_cover
    // Exercise a decode miss routed to the configured default downstream.
    `BR_COVER(default_route_c, downstream_req_start && magic_d_is_default && !upstream_addr_hit)
  end else begin : gen_decode_miss_cover
    // Exercise a decode miss completed locally with PSLVERR.
    `BR_COVER(decode_miss_c, decode_miss && upstream_penable && upstream_pready && upstream_pslverr)
  end

endmodule : br_apb_demux_fpv_monitor

bind br_apb_demux br_apb_demux_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .NumDownstreams(NumDownstreams),
    .NumRetimeStages(NumRetimeStages),
    .HasDefaultDownstream(HasDefaultDownstream),
    .RequirePowerOfTwoAlignedRanges(RequirePowerOfTwoAlignedRanges),
    .NormalizeDownstreamAddress(NormalizeDownstreamAddress),
    .UpstreamAddrMask(UpstreamAddrMask),
    .DownstreamAddrMask(DownstreamAddrMask)
) monitor (.*);
