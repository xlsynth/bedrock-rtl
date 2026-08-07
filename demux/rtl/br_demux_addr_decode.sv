// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Address Decoder for Protocol Demultiplexers
//
// Decodes an upstream address into a one-hot downstream selection and applies
// optional address normalization and masking to forwarded downstream
// addresses. Address ranges are configurable inputs and are checked whenever
// addr_valid is asserted.

`include "br_asserts_internal.svh"

module br_demux_addr_decode #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int NumDownstreams = 1,  // Must be at least 1
    parameter bit HasDefaultDownstream = 0,
    localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams,
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter bit RequirePowerOfTwoAlignedRanges[NumAddressRanges] = '{default: 1},
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter bit NormalizeDownstreamAddress[NumAddressRanges] = '{default: 0},
    parameter logic [AddrWidth-1:0] UpstreamAddrMask = '1,
    parameter logic [NumDownstreams-1:0][AddrWidth-1:0] DownstreamAddrMask = '1
) (
    // Used only by integration assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Used only by integration assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    // Used only by integration assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic addr_valid,
    input logic [AddrWidth-1:0] upstream_addr,

    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_size,

    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_in,
    output logic [NumDownstreams-1:0] select_onehot,
    output logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_out
);
  // Integration Checks

  `BR_ASSERT_STATIC(legal_num_downstreams_a, NumDownstreams >= 1 + HasDefaultDownstream)
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)

  logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_limit;
  logic [NumAddressRanges-1:0] downstream_addr_range_disabled;

  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_range_check
    assign downstream_addr_limit[i] = downstream_addr_base[i] + downstream_addr_size[i] - 1'b1;
    assign downstream_addr_range_disabled[i] = downstream_addr_size[i] == '0;

    if (AddrWidth > 1) begin : gen_multi_bit_addr_range_check
      `BR_ASSERT_INTG(downstream_addr_range_no_overflow_a,
                      addr_valid |-> downstream_addr_range_disabled[i] ||
                          downstream_addr_limit[i] >= downstream_addr_base[i])

      if (RequirePowerOfTwoAlignedRanges[i]) begin : gen_power_of_two_aligned_range_check
        `BR_ASSERT_INTG(downstream_addr_size_power_of_two_a,
                        addr_valid |-> $onehot0(downstream_addr_size[i]))
        `BR_ASSERT_INTG(downstream_addr_base_aligned_a,
                        addr_valid |-> downstream_addr_range_disabled[i] ||
                (downstream_addr_base[i] & (downstream_addr_size[i] - 1'b1)) == '0)
        if (DownstreamAddrMask[i] != '1) begin : gen_downstream_addr_mask_check
          `BR_ASSERT_INTG(downstream_addr_mask_preserves_offsets_a,
                          addr_valid |-> downstream_addr_range_disabled[i] ||
                  ((downstream_addr_size[i] - 1'b1) & ~DownstreamAddrMask[i]) == '0)
        end
      end
    end
  end

  for (genvar i = 0; i < NumAddressRanges - 1; i++) begin : gen_range_overlap_check_i
    for (genvar j = i + 1; j < NumAddressRanges; j++) begin : gen_range_overlap_check_j
      `BR_ASSERT_INTG(downstream_addr_range_overlap_a,
                      addr_valid |-> downstream_addr_range_disabled[i] ||
                          downstream_addr_range_disabled[j] ||
                          downstream_addr_limit[i] < downstream_addr_base[j] ||
                          downstream_addr_base[i] > downstream_addr_limit[j])
    end
  end

  // Implementation

  logic [AddrWidth-1:0] upstream_addr_masked;

  assign upstream_addr_masked = upstream_addr & UpstreamAddrMask;

  // ri lint_check_off PARAM_BIT_SEL
  for (genvar i = 0; i < NumAddressRanges; i++) begin : gen_downstream_addr_translate
    assign select_onehot[i] = !downstream_addr_range_disabled[i] &&
                              (upstream_addr_masked >= downstream_addr_base[i]) &&
                              (upstream_addr_masked <= downstream_addr_limit[i]);

    if (NormalizeDownstreamAddress[i]) begin : gen_normalize_downstream_address
      assign downstream_addr_out[i] =
          (downstream_addr_in[i] - downstream_addr_base[i]) & DownstreamAddrMask[i];
    end else begin : gen_passthrough_downstream_address
      assign downstream_addr_out[i] = downstream_addr_in[i] & DownstreamAddrMask[i];
    end
  end

  if (HasDefaultDownstream) begin : gen_default_downstream_addr_translate
    assign select_onehot[NumDownstreams-1] = !(|select_onehot[NumAddressRanges-1:0]);
    assign downstream_addr_out[NumDownstreams-1] =
        downstream_addr_in[NumDownstreams-1] & DownstreamAddrMask[NumDownstreams-1];
  end
  // ri lint_check_on PARAM_BIT_SEL

endmodule : br_demux_addr_decode
