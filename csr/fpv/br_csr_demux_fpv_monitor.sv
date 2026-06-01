// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL CSR Demux FPV Monitor
//
// This checker verifies the address-decoding wrapper around
// br_csr_demux_select_onehot. It checks that decoded ranges are legal and
// non-overlapping, that requests matching an arbitrary downstream are forwarded
// with the expected payload and translated address, that decode misses either go
// to the default downstream or return DECERR, and that downstream responses and
// aborts make forward progress back through the demux.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_csr_demux_fpv_monitor #(
    parameter int AddrWidth = 1,
    parameter int DataWidth = 32,
    parameter int NumDownstreams = 1,
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
    parameter bit HasDefaultDownstream = 0,
    localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams,
    parameter bit RequirePowerOfTwoAlignedRanges[NumAddressRanges] = '{default: 1},
    parameter bit NormalizeDownstreamAddress[NumAddressRanges] = '{default: 0},
    parameter logic [AddrWidth-1:0] UpstreamAddrMask = '1,
    parameter logic [NumDownstreams-1:0][AddrWidth-1:0] DownstreamAddrMask = '1,
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic upstream_req_valid,
    input logic upstream_req_write,
    input logic [AddrWidth-1:0] upstream_req_addr,
    input logic [DataWidth-1:0] upstream_req_wdata,
    input logic [StrobeWidth-1:0] upstream_req_wstrb,
    input logic upstream_req_privileged,
    input logic upstream_req_secure,
    input logic upstream_req_abort,

    input logic upstream_resp_valid,
    input logic [DataWidth-1:0] upstream_resp_rdata,
    input logic upstream_resp_decerr,
    input logic upstream_resp_slverr,

    // Base address and size for each explicit downstream route.
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_size,

    input logic [NumDownstreams-1:0] downstream_req_valid,
    input logic [NumDownstreams-1:0] downstream_req_write,
    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr,
    input logic [NumDownstreams-1:0][DataWidth-1:0] downstream_req_wdata,
    input logic [NumDownstreams-1:0][StrobeWidth-1:0] downstream_req_wstrb,
    input logic [NumDownstreams-1:0] downstream_req_privileged,
    input logic [NumDownstreams-1:0] downstream_req_secure,
    input logic [NumDownstreams-1:0] downstream_req_abort,

    input logic [NumDownstreams-1:0] downstream_resp_valid,
    input logic [NumDownstreams-1:0][DataWidth-1:0] downstream_resp_rdata,
    input logic [NumDownstreams-1:0] downstream_resp_decerr,
    input logic [NumDownstreams-1:0] downstream_resp_slverr
);

  // 3 = req_write, req_privileged, req_secure
  localparam int ReqWidth = 3 + AddrWidth + DataWidth + StrobeWidth;
  localparam int DownstreamWidth = NumDownstreams == 1 ? 1 : $clog2(NumDownstreams);

  logic upstream_req_pending;
  logic upstream_req_pending_next;
  logic [NumDownstreams-1:0] downstream_req_pending;
  logic [NumDownstreams-1:0] downstream_req_pending_next;
  logic [DownstreamWidth-1:0] d;
  logic magic_upstream_req_valid;
  logic [31:0] abort_cntr;
  logic [31:0] abort_cntr_next;
  logic addr_req_pending_d;
  logic addr_req_pending_d_next;
  logic [AddrWidth-1:0] upstream_req_addr_masked;
  logic upstream_addr_hit;
  logic upstream_decerr_valid;
  logic fv_downstream_resp_valid;
  logic [NumDownstreams:0] downstream_resp_vec;
  logic [DownstreamWidth:0] downstream_resp_id;
  logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_limit;
  logic [NumAddressRanges-1:0] downstream_addr_range_disabled;
  logic [AddrWidth-1:0] expected_downstream_req_addr;
  logic [DataWidth-1:0] fv_downstream_resp_rdata;
  logic fv_downstream_resp_decerr;
  logic fv_downstream_resp_slverr;

  assign upstream_req_pending_next = (upstream_req_pending && !upstream_resp_valid) ||
                                     upstream_req_valid;

  `BR_REG(upstream_req_pending, upstream_req_pending_next)

  always_comb begin
    downstream_req_pending_next = downstream_req_pending;
    for (int i = 0; i < NumDownstreams; i++) begin
      if (downstream_req_valid[i]) begin
        downstream_req_pending_next[i] = 1'b1;
      end else if (downstream_resp_valid[i]) begin
        downstream_req_pending_next[i] = 1'b0;
      end
    end
  end

  `BR_REG(downstream_req_pending, downstream_req_pending_next)

  logic addr_match_d;
  logic d_is_default;

  // Mask applied to the upstream address prior to decoding.
  assign upstream_req_addr_masked = upstream_req_addr & UpstreamAddrMask;

  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_downstream_addr_limit
    assign downstream_addr_limit[i] = downstream_addr_base[i] + downstream_addr_size[i] - 1'b1;
    assign downstream_addr_range_disabled[i] = downstream_addr_size[i] == '0;
  end

  always_comb begin
    addr_match_d = 1'b0;
    for (int i = 0; i < NumAddressRanges; i++) begin
      if (d == DownstreamWidth'(i)) begin
        addr_match_d = !downstream_addr_range_disabled[i] &&
                       (upstream_req_addr_masked >= downstream_addr_base[i]) &&
                       (upstream_req_addr_masked <= downstream_addr_limit[i]);
        break;
      end
    end
  end

  assign d_is_default = HasDefaultDownstream && (d == DownstreamWidth'(NumAddressRanges));
  assign magic_upstream_req_valid = upstream_req_valid &&
                                    (addr_match_d || (d_is_default && !upstream_addr_hit));
  assign addr_req_pending_d_next = (addr_req_pending_d || magic_upstream_req_valid) &&
                                   !downstream_req_valid[d];

  // Track when a request selected for d is still in the downstream request retime path.
  `BR_REG(addr_req_pending_d, addr_req_pending_d_next)

  // Expected forwarded downstream address after optional rebasing and masking.
  always_comb begin
    expected_downstream_req_addr = upstream_req_addr;
    for (int i = 0; i < NumAddressRanges; i++) begin
      if (d == DownstreamWidth'(i)) begin
        expected_downstream_req_addr = NormalizeDownstreamAddress[i] ?
                                       upstream_req_addr - downstream_addr_base[i] :
                                       upstream_req_addr;
        break;
      end
    end
    expected_downstream_req_addr &= DownstreamAddrMask[d];
  end

  assign abort_cntr_next = abort_cntr + upstream_req_abort - downstream_req_abort[d];

  // Count aborts through an arbitrary downstream retime path.
  `BR_REG(abort_cntr, abort_cntr_next)

  always_comb begin
    upstream_addr_hit = 1'b0;
    for (int i = 0; i < NumAddressRanges; i++) begin
      if (!downstream_addr_range_disabled[i] &&
          (upstream_req_addr_masked >= downstream_addr_base[i]) &&
          (upstream_req_addr_masked <= downstream_addr_limit[i])) begin
        upstream_addr_hit = 1'b1;
        break;
      end
    end
  end

  if (HasDefaultDownstream) begin : gen_no_decerr
    assign upstream_decerr_valid = 1'b0;
  end else begin : gen_decerr
    assign upstream_decerr_valid = upstream_req_valid && !upstream_addr_hit;
  end

  assign downstream_resp_vec = {upstream_decerr_valid, downstream_resp_valid};
  assign fv_downstream_resp_valid = |downstream_resp_vec;

  always_comb begin
    downstream_resp_id = '0;
    for (int i = 0; i < NumDownstreams + 1; i++) begin
      if (downstream_resp_vec[i]) begin
        downstream_resp_id = i;
        break;
      end
    end
  end

  assign fv_downstream_resp_rdata = downstream_resp_id == NumDownstreams ?
                                    DataWidth'(0) : downstream_resp_rdata[downstream_resp_id];
  assign fv_downstream_resp_decerr = downstream_resp_id == NumDownstreams ?
                                     1'b1 : downstream_resp_decerr[downstream_resp_id];
  assign fv_downstream_resp_slverr = downstream_resp_id == NumDownstreams ?
                                     1'b0 : downstream_resp_slverr[downstream_resp_id];

  // ----------FV assumptions----------
  // Pick an arbitrary downstream interface to prove the request path generically.
  `BR_ASSUME(constant_d_a, $stable(d) && d < NumDownstreams)

  // The upstream agent issues at most one request until a response returns.
  `BR_ASSUME(only_one_outstanding_req_upstream_a, upstream_req_pending |-> !upstream_req_valid)

  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_addr
    // Normalized range bases are used after retiming, so keep the selected base
    // stable until the selected request reaches its downstream port.
    if (NormalizeDownstreamAddress[i] && (NumRetimeStages[i] > 0)) begin : gen_normalized_addr
      `BR_ASSUME(
          addr_base_stable_until_req_forwarded_a,
          addr_req_pending_d && (d == DownstreamWidth'(i)) |-> $stable(downstream_addr_base[i]))
    end

    // Enabled ranges must not overflow the address width.
    `BR_ASSUME(legal_addr_range_a,
               upstream_req_valid |-> downstream_addr_range_disabled[i] ||
            downstream_addr_limit[i] >= downstream_addr_base[i])

    if (RequirePowerOfTwoAlignedRanges[i]) begin : gen_power_of_two_aligned_addr
      // Enabled power-of-two ranges have exactly one size bit set.
      `BR_ASSUME(addr_size_power_of_two_a, upstream_req_valid |-> $onehot0(downstream_addr_size[i]))

      // Enabled power-of-two ranges start on their natural alignment.
      `BR_ASSUME(addr_base_aligned_a,
                 upstream_req_valid |-> downstream_addr_range_disabled[i] ||
                     (downstream_addr_base[i] & (downstream_addr_size[i] - 1'b1)) == '0)

      // Downstream masks must preserve all enabled in-range offset bits.
      `BR_ASSUME(addr_mask_preserves_offsets_a,
                 upstream_req_valid |-> downstream_addr_range_disabled[i] ||
                     ((downstream_addr_size[i] - 1'b1) & ~DownstreamAddrMask[i]) == '0)
    end
  end

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_resp
    // Downstreams only respond to a request that is outstanding on that port.
    `BR_ASSUME(no_spurious_downstream_resp_a,
               downstream_resp_valid[i] |-> downstream_req_pending[i])
  end

  for (genvar i = 0; i < NumAddressRanges - 1; i++) begin : gen_i
    for (genvar j = i + 1; j < NumAddressRanges; j++) begin : gen_j
      // Explicit address ranges do not overlap.
      `BR_ASSUME(no_overlapping_addr_a,
                 upstream_req_valid |-> downstream_addr_range_disabled[i] ||
                     downstream_addr_range_disabled[j] ||
                     downstream_addr_limit[i] < downstream_addr_base[j] ||
                     downstream_addr_base[i] > downstream_addr_limit[j])
    end
  end

  // ----------FV assertions----------
  // Requests decoded to the arbitrary downstream preserve payload and translated address.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ReqWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) req_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(magic_upstream_req_valid),
      .incoming_data({
        upstream_req_write,
        upstream_req_privileged,
        upstream_req_secure,
        expected_downstream_req_addr,
        upstream_req_wdata,
        upstream_req_wstrb
      }),
      .outgoing_vld(downstream_req_valid[d]),
      .outgoing_data({
        downstream_req_write[d],
        downstream_req_privileged[d],
        downstream_req_secure[d],
        downstream_req_addr[d],
        downstream_req_wdata[d],
        downstream_req_wstrb[d]
      })
  );

  // Downstream or internal DECERR response data is returned upstream.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(DataWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) resp_data_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_downstream_resp_valid),
      .incoming_data(fv_downstream_resp_rdata),
      .outgoing_vld(upstream_resp_valid),
      .outgoing_data(upstream_resp_rdata)
  );

  // Downstream or internal DECERR slave-error status is returned upstream.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(1),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) resp_slverr_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_downstream_resp_valid),
      .incoming_data(fv_downstream_resp_slverr),
      .outgoing_vld(upstream_resp_valid),
      .outgoing_data(upstream_resp_slverr)
  );

  // Downstream or internal DECERR decode-error status is returned upstream.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(1),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) resp_decerr_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_downstream_resp_valid),
      .incoming_data(fv_downstream_resp_decerr),
      .outgoing_vld(upstream_resp_valid),
      .outgoing_data(upstream_resp_decerr)
  );

  // A downstream abort cannot appear unless an upstream abort is pending through that retime path.
  `BR_ASSERT(no_spurious_abort_a,
             (abort_cntr == 'd0) && !upstream_req_abort |-> !downstream_req_abort[d])

  // At most one downstream or internal DECERR response can drive the upstream response mux.
  `BR_ASSERT(resp_upstream_decerr_onehot_a, $onehot0(downstream_resp_vec))

  // The demux does not issue a second request to a downstream with one still outstanding.
  `BR_ASSERT(only_one_outstanding_req_downstream_a,
             downstream_req_pending[d] |-> !downstream_req_valid[d])

  // Every upstream abort eventually reaches the selected downstream retime path.
  `BR_ASSERT(no_deadlock_abort_a, upstream_req_abort |-> s_eventually downstream_req_abort[d])

  // Every request decoded to the arbitrary downstream eventually reaches that port.
  `BR_ASSERT(no_deadlock_downstream_req_a,
             magic_upstream_req_valid |-> s_eventually downstream_req_valid[d])

  // Every downstream or internal DECERR response eventually reaches the upstream interface.
  `BR_ASSERT(no_deadlock_upstream_resp_a,
             fv_downstream_resp_valid |-> s_eventually upstream_resp_valid)

endmodule : br_csr_demux_fpv_monitor

bind br_csr_demux br_csr_demux_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .NumDownstreams(NumDownstreams),
    .NumRetimeStages(NumRetimeStages),
    .HasDefaultDownstream(HasDefaultDownstream),
    .RequirePowerOfTwoAlignedRanges(RequirePowerOfTwoAlignedRanges),
    .NormalizeDownstreamAddress(NormalizeDownstreamAddress),
    .UpstreamAddrMask(UpstreamAddrMask),
    .DownstreamAddrMask(DownstreamAddrMask)
) monitor (.*);
