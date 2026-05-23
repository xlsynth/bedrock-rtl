// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Address-Decoding SCB Demux
//
// Routes SCB requests to the correct downstream interface based on the request
// address. Address ranges are provided as inputs so straps can select the
// decoded map. Optional masks provide local address views while decoding and
// while forwarding requests downstream.
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
    // If 1, assert that every decoded range is power-of-two sized and naturally
    // aligned, allowing mask-based local address views. Set to 0 for deliberately
    // non-aligned maps; this module does not rebase addresses.
    parameter bit RequirePowerOfTwoAlignedRanges = 1,
    // Mask applied to the upstream address prior to decoding.
    parameter logic [AddrWidth-1:0] UpstreamAddrMask = '1,
    // Mask applied to each forwarded downstream request address.
    parameter logic [NumDownstreams-1:0][AddrWidth-1:0] DownstreamAddrMask = '1,
    localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams,
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
    // inclusive bound is base + size - 1. The last downstream has no decoded
    // range when HasDefaultDownstream is set.
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

  // Derive inclusive route bounds with one extra bit to detect overflow.
  logic [NumAddressRanges-1:0][  AddrWidth:0] downstream_addr_limit_ext;
  logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_limit;

  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_range_check
    assign downstream_addr_limit_ext[i] = downstream_addr_base[i] + downstream_addr_size[i] - 1'b1;
    assign downstream_addr_limit[i] = downstream_addr_limit_ext[i][AddrWidth-1:0];

    `BR_ASSERT_INTG(legal_downstream_addr_size_a, $fell(rst) |-> downstream_addr_size[i] > '0)
    `BR_ASSERT_INTG(downstream_addr_range_no_overflow_a,
                    $fell(rst) |-> !downstream_addr_limit_ext[i][AddrWidth])

    if (RequirePowerOfTwoAlignedRanges) begin : gen_power_of_two_aligned_range_check
      `BR_ASSERT_INTG(
          downstream_addr_size_power_of_two_a,
          $fell(rst) |-> (downstream_addr_size[i] & (downstream_addr_size[i] - 1'b1)) == '0)
      `BR_ASSERT_INTG(
          downstream_addr_base_aligned_a,
          $fell(rst) |-> (downstream_addr_base[i] & (downstream_addr_size[i] - 1'b1)) == '0)
    end
  end

  for (genvar i = 0; i < NumAddressRanges - 1; i++) begin : gen_range_overlap_check_i
    for (genvar j = i + 1; j < NumAddressRanges; j++) begin : gen_range_overlap_check_j
      `BR_ASSERT_INTG(downstream_addr_range_overlap_a,
                      $fell(
                          rst
                      ) |-> downstream_addr_limit[i] < downstream_addr_base[j] ||
                          downstream_addr_base[i] > downstream_addr_limit[j])
    end
  end

  // Implementation

  logic [AddrWidth-1:0] upstream_req_addr_masked;
  logic [NumAddressRanges-1:0] select_onehot;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr_unmasked;

  assign upstream_req_addr_masked = upstream_req_addr & UpstreamAddrMask;

  // Request address decoding
  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_select
    assign select_onehot[i] =
        (upstream_req_addr_masked >= downstream_addr_base[i]) &&
        (upstream_req_addr_masked <= downstream_addr_limit[i]);
  end

  // Parameter array indexing selects one fixed outgoing mask per generated route.
  // ri lint_check_off PARAM_BIT_SEL
  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_addr_mask
    assign downstream_req_addr[i] = downstream_req_addr_unmasked[i] & DownstreamAddrMask[i];
  end
  // ri lint_check_on PARAM_BIT_SEL

  br_csr_demux_select_onehot #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .NumDownstreams(NumDownstreams),
      .NumRetimeStages(NumRetimeStages),
      .HasDefaultDownstream(HasDefaultDownstream)
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
