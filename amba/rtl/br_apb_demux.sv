// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Address-Decoding APB Demux
//
// Routes APB transfers to the correct downstream interface based on PADDR.
// Address ranges, optional masking, normalization, and default routing use the
// protocol-neutral br_demux_addr_decode helper. APB fanout, timing, and
// response handling use br_apb_demux_select_onehot.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_apb_demux #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int NumDownstreams = 1,  // Must be at least 1
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
    // When set, the final downstream receives every address that misses the
    // explicit ranges. Otherwise, misses complete with PSLVERR.
    parameter bit HasDefaultDownstream = 0,
    localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams,
    // Require enabled ranges to be power-of-two sized and naturally aligned.
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter bit RequirePowerOfTwoAlignedRanges[NumAddressRanges] = '{default: 1},
    // Rebase each explicit downstream address before applying its output mask.
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter bit NormalizeDownstreamAddress[NumAddressRanges] = '{default: 0},
    // Mask used only for address decode; forwarded addresses remain unmasked.
    parameter logic [AddrWidth-1:0] UpstreamAddrMask = '1,
    // Mask applied to each forwarded address after optional normalization.
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
    // TODO(twabbott): Parameterize APB data/strobe widths once br_amba_apb_timing_slice supports it.
    input logic [31:0] upstream_pwdata,
    output logic [31:0] upstream_prdata,
    output logic upstream_pready,
    output logic upstream_pslverr,

    // Configurable ranges must remain stable while an APB transfer is pending.
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_size,

    output logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_paddr,
    output logic [NumDownstreams-1:0] downstream_psel,
    output logic [NumDownstreams-1:0] downstream_penable,
    output logic [NumDownstreams-1:0][br_amba::ApbProtWidth-1:0] downstream_pprot,
    output logic [NumDownstreams-1:0][3:0] downstream_pstrb,
    output logic [NumDownstreams-1:0] downstream_pwrite,
    output logic [NumDownstreams-1:0][31:0] downstream_pwdata,
    input logic [NumDownstreams-1:0][31:0] downstream_prdata,
    input logic [NumDownstreams-1:0] downstream_pready,
    input logic [NumDownstreams-1:0] downstream_pslverr
);
  // Integration Checks

  logic upstream_request_pending;

  assign upstream_request_pending = upstream_psel && (!upstream_penable || !upstream_pready);

  `BR_ASSERT_STATIC(legal_num_downstreams_a, NumDownstreams >= 1 + HasDefaultDownstream)
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 12)
  `BR_ASSERT_INTG(addr_map_stable_while_pending_a, upstream_request_pending |=> $stable
                                                   ({downstream_addr_base, downstream_addr_size}))
  `BR_UNUSED(upstream_request_pending)

  // Implementation

  logic [NumDownstreams-1:0] select_onehot;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_paddr_unmasked;

  br_demux_addr_decode #(
      .AddrWidth(AddrWidth),
      .NumDownstreams(NumDownstreams),
      .HasDefaultDownstream(HasDefaultDownstream),
      .RequirePowerOfTwoAlignedRanges(RequirePowerOfTwoAlignedRanges),
      .NormalizeDownstreamAddress(NormalizeDownstreamAddress),
      .UpstreamAddrMask(UpstreamAddrMask),
      .DownstreamAddrMask(DownstreamAddrMask)
  ) br_demux_addr_decode (
      .clk,
      .rst,
      .addr_valid(upstream_psel),
      .upstream_addr(upstream_paddr),
      .downstream_addr_base,
      .downstream_addr_size,
      .downstream_addr_in(downstream_paddr_unmasked),
      .select_onehot,
      .downstream_addr_out(downstream_paddr)
  );

  br_apb_demux_select_onehot #(
      .AddrWidth(AddrWidth),
      .NumDownstreams(NumDownstreams),
      .EnableDecodeError(!HasDefaultDownstream),
      .NumRetimeStages(NumRetimeStages)
  ) br_apb_demux_select_onehot (
      .clk,
      .rst,
      .select_onehot,
      .upstream_paddr,
      .upstream_psel,
      .upstream_penable,
      .upstream_pprot,
      .upstream_pstrb,
      .upstream_pwrite,
      .upstream_pwdata,
      .upstream_prdata,
      .upstream_pready,
      .upstream_pslverr,
      .downstream_paddr(downstream_paddr_unmasked),
      .downstream_psel,
      .downstream_penable,
      .downstream_pprot,
      .downstream_pstrb,
      .downstream_pwrite,
      .downstream_pwdata,
      .downstream_prdata,
      .downstream_pready,
      .downstream_pslverr
  );

endmodule : br_apb_demux
