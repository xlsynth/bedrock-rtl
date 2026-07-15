// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Address-Decoding SCB Demux
//
// Routes SCB requests to the correct downstream interface based on the request
// address. Address ranges are configurable inputs; each request is decoded
// from their current values. Optional masks may be applied while decoding and
// while forwarding requests downstream. Forwarded addresses for explicit
// ranges may independently be normalized relative to their range base.
// Selection-based SCB routing and response handling are implemented by
// br_csr_demux_select_onehot.
//

`include "br_asserts_internal.svh"

module br_csr_demux #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 32,  // Must be 32 or 64
    parameter int NumDownstreams = 1,  // Must be at least 1
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
    // If 1, the last downstream SCB request port (NumDownstreams-1)
    // will take any request that doesn't match the address base and bound
    // of any of the other downstream ports.
    // If 0, a request with an address that doesn't match any downstream address range
    // will result in a response with decerr=1.
    parameter bit HasDefaultDownstream = 0,
    localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams,
    // If 1 for an enabled decoded range, assert that its size is a power of two
    // and its base is naturally aligned to that size.
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter bit RequirePowerOfTwoAlignedRanges[NumAddressRanges] = '{default: 1},
    // If 1 for a decoded range, normalize its forwarded address by subtracting
    // its range base before applying its outgoing mask.
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter bit NormalizeDownstreamAddress[NumAddressRanges] = '{default: 0},
    // Mask applied to the upstream address only for route decoding. Forwarded
    // addresses start from the unmasked upstream address.
    parameter logic [AddrWidth-1:0] UpstreamAddrMask = '1,
    // Mask applied to each forwarded downstream request address, after
    // normalization where applicable.
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

    output logic upstream_resp_valid,
    output logic [DataWidth-1:0] upstream_resp_rdata,
    output logic upstream_resp_decerr,
    output logic upstream_resp_slverr,

    // Base address and size for each decoded downstream route. The decoded
    // inclusive bound is base + size - 1. A zero size disables the route. A
    // full address-map-sized route cannot be represented by AddrWidth-bit size.
    // The last downstream has no decoded range when HasDefaultDownstream is set.
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_size,

    output logic [NumDownstreams-1:0] downstream_req_valid,
    output logic [NumDownstreams-1:0] downstream_req_write,
    output logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr,
    output logic [NumDownstreams-1:0][DataWidth-1:0] downstream_req_wdata,
    output logic [NumDownstreams-1:0][StrobeWidth-1:0] downstream_req_wstrb,
    output logic [NumDownstreams-1:0] downstream_req_privileged,
    output logic [NumDownstreams-1:0] downstream_req_secure,
    output logic [NumDownstreams-1:0] downstream_req_abort,

    input logic [NumDownstreams-1:0] downstream_resp_valid,
    input logic [NumDownstreams-1:0][DataWidth-1:0] downstream_resp_rdata,
    input logic [NumDownstreams-1:0] downstream_resp_decerr,
    input logic [NumDownstreams-1:0] downstream_resp_slverr
);
  // Integration Checks

  // There must be at least one non-default downstream port
  `BR_ASSERT_STATIC(legal_num_downstreams_a, NumDownstreams >= 1 + HasDefaultDownstream)
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth == 32 || DataWidth == 64)

  // Implementation

  logic [NumDownstreams-1:0] select_onehot;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr_unmasked;

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
      .addr_valid(upstream_req_valid),
      .upstream_addr(upstream_req_addr),
      .downstream_addr_base,
      .downstream_addr_size,
      .downstream_addr_in(downstream_req_addr_unmasked),
      .select_onehot,
      .downstream_addr_out(downstream_req_addr)
  );

  br_csr_demux_select_onehot #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .NumDownstreams(NumDownstreams),
      .NumRetimeStages(NumRetimeStages)
  ) br_csr_demux_select_onehot (
      .clk,
      .rst,
      .select_onehot,
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
      .downstream_req_valid,
      .downstream_req_write,
      .downstream_req_addr(downstream_req_addr_unmasked),
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

endmodule : br_csr_demux
