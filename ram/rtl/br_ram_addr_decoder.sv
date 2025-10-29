// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Address Decoder
//
// Decodes and steers an input address and data to one output tile based on the
// most-significant bits of the address.
//
// Works for any RAM depth >= 2 and any number of output tiles >= 1 that evenly
// divides the RAM depth. If RAM depth is a power-of-2 then the implementation is optimized.
//
// The latency is given by Stages. If Stages is 0, then the module is purely combinational;
// if 1, then there is a single pipeline register stage. Values greater than 1 work but don't
// pipeline the logic inside the decoding tree, they just retime the decoded outputs.
//
// If EnableDatapath is 1, then the datapath is implemented. The in_data_valid signal
// must be in lockstep with in_valid; it is provided separately so that the datapath
// can be clock gated when not used (e.g., for accessing a shared read-write RAM port)
// If EnableDatapath is 0, then asserts that in_data_valid is always 0.

`include "br_asserts_internal.svh"
`include "br_tieoff.svh"
`include "br_unused.svh"

module br_ram_addr_decoder #(
    // Depth of the RAM. Must be at least 1.
    parameter int Depth = 1,
    // Sideband signals to pipeline in lockstep with the address decoding.
    // Safe to tie-off if not used. Must be at least 1.
    parameter int DataWidth = 1,
    // Number of output address tiles. Must be at least 1 and evenly divide Depth.
    parameter int Tiles = 1,
    // Pipeline depth. Must be at least 0.
    // Values greater than 1 are of dubious utility but don't hurt anything.
    parameter int Stages = 0,
    // If 1, then the datapath is implemented. Otherwise, asserts that in_valid is always 0.
    parameter bit EnableDatapath = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int InputAddressWidth = br_math::clamped_clog2(Depth),
    localparam int OutputAddressWidth = br_math::clamped_clog2(TileDepth)
) (
    // Posedge-triggered clock.
    // Can be unused if Stages == 0.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 clk,
    // Synchronous active-high reset.
    // Can be unused if Stages == 0.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 rst,
    // Input address and data.
    input  logic                                                 in_valid,
    // ri lint_check_waive UNBALANCED_FANOUT
    input  logic [InputAddressWidth-1:0]                         in_addr,
    // in_data_valid is provided so that the datapath can be clock gated.
    //
    // When EnableDatapath is 1:
    //   * in_data_valid can only be 1 if in_valid is also 1.
    //   * If this address decoder is used for only reads: tie in_data_valid to 0.
    //   * If this address decoder is used for only writes: tie in_data_valid to 1.
    //   * Otherwise, connect it to a corresponding write enable signal.
    //
    // When EnableDatapath is 0:
    //   * in_data_valid must be tied to 0.
    input  logic                                                 in_data_valid,
    input  logic [        DataWidth-1:0]                         in_data,
    // Output tile addresses and data.
    output logic [            Tiles-1:0]                         out_valid,
    output logic [            Tiles-1:0][OutputAddressWidth-1:0] out_addr,
    // When EnableDatapath is 1:
    // * out_data_valid may only be 1 if out_valid is also 1.
    //
    // When EnableDatapath is 0:
    // * out_data_valid is tied to 0.
    output logic [            Tiles-1:0]                         out_data_valid,
    output logic [            Tiles-1:0][         DataWidth-1:0] out_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte1_a, Depth >= 1)
  `BR_ASSERT_STATIC(data_width_gte1_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(tiles_gte1_a, Tiles >= 1)
  `BR_ASSERT_STATIC(tiles_evenly_divides_depth_a, (Tiles * TileDepth) == Depth)
  `BR_ASSERT_STATIC(stages_gte0_a, Stages >= 0)

  `BR_ASSERT_INTG(in_addr_in_range_a, in_valid |-> in_addr < Depth)

  if (EnableDatapath) begin : gen_datapath_checks_intg
    `BR_ASSERT_INTG(in_data_valid_a, in_data_valid |-> in_valid)
  end else begin : gen_no_datapath_checks_intg
    `BR_ASSERT_INTG(in_data_valid_tied_to_0_a, in_data_valid == 0)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Base case: single tile, i.e., just a simple delay register
  if (Tiles == 1) begin : gen_tiles_eq1
    `BR_ASSERT_STATIC(output_address_width_ok_a, OutputAddressWidth == InputAddressWidth)

    br_delay_valid #(
        .Width(OutputAddressWidth),
        .NumStages(Stages),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_delay_valid_addr (
        .clk,
        .rst,
        .in_valid(in_valid),
        .in(in_addr),
        .out_valid(out_valid),
        .out(out_addr),
        .out_valid_stages(),  // unused
        .out_stages()  // unused
    );

    if (EnableDatapath) begin : gen_datapath
      br_delay_valid #(
          .Width(DataWidth),
          .NumStages(Stages),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_delay_valid_data (
          .clk,
          .rst,
          .in_valid(in_data_valid),
          .in(in_data),
          .out_valid(out_data_valid),
          .out(out_data),
          .out_valid_stages(),  // unused
          .out_stages()  // unused
      );

    end else begin : gen_no_datapath
      `BR_UNUSED(in_data_valid)
      `BR_UNUSED(in_data)
      `BR_TIEOFF_ZERO(out_data_valid)
      `BR_TIEOFF_ZERO(out_data)
    end

    // Common case: multiple tiles, i.e., requires decoding to one of them (replicated delay registers)
  end else begin : gen_tiles_gt1
    if (TileDepth > 1) begin : gen_address_width_check
      `BR_ASSERT_STATIC(output_address_width_ok_a, OutputAddressWidth < InputAddressWidth)
    end

    logic [Tiles-1:0]                         internal_out_valid;
    logic [Tiles-1:0][OutputAddressWidth-1:0] internal_out_addr;
    logic [Tiles-1:0]                         internal_out_data_valid;
    logic [Tiles-1:0][         DataWidth-1:0] internal_out_data;

    if (TileDepth == 1) begin : gen_tile_depth_eq1
      // If each tile only has one entry, the out valid is just a onehot
      // decoding of the input address. The out address is always 0.

      br_demux_bin #(
          .NumSymbolsOut(Tiles),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_demux_bin_addr (
          .select(in_addr),
          .in_valid(in_valid),
          .in('0),  // unused
          .out_valid(internal_out_valid),
          .out()  // unused
      );

      assign internal_out_addr = '0;

      if (EnableDatapath) begin : gen_datapath
        br_demux_bin #(
            .NumSymbolsOut(Tiles),
            .SymbolWidth(DataWidth),
            .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
        ) br_demux_bin_data (
            .select(in_addr),
            .in_valid(in_data_valid),
            .in(in_data),
            .out_valid(internal_out_data_valid),
            .out(internal_out_data)
        );

      end else begin : gen_no_datapath
        `BR_UNUSED(in_data_valid)
        `BR_UNUSED(in_data)
        `BR_TIEOFF_ZERO(internal_out_data_valid)
        `BR_TIEOFF_ZERO(internal_out_data)
      end

    end else if (br_math::is_power_of_2(Depth)) begin : gen_demux_impl
      // If Depth is a power of 2 (and Tiles evenly divides it), then we know we can
      // decode the address by looking only at the MSBs as the tile select bits,
      // and simply slice them off.
      localparam int TileSelectWidth = $clog2(Tiles);
      localparam int SelectMsb = InputAddressWidth - 1;
      localparam int SelectLsb = (SelectMsb - TileSelectWidth) + 1;
      `BR_ASSERT_STATIC(select_check_a, SelectMsb >= SelectLsb)

      br_demux_bin #(
          .NumSymbolsOut(Tiles),
          .SymbolWidth(OutputAddressWidth),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_demux_bin_addr (
          .select(in_addr[SelectMsb:SelectLsb]),
          .in_valid(in_valid),
          .in(in_addr[OutputAddressWidth-1:0]),
          .out_valid(internal_out_valid),
          .out(internal_out_addr)
      );

      if (EnableDatapath) begin : gen_datapath
        br_demux_bin #(
            .NumSymbolsOut(Tiles),
            .SymbolWidth(DataWidth),
            .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
        ) br_demux_bin_data (
            .select(in_addr[SelectMsb:SelectLsb]),
            .in_valid(in_data_valid),
            .in(in_data),
            .out_valid(internal_out_data_valid),
            .out(internal_out_data)
        );

      end else begin : gen_no_datapath
        `BR_UNUSED(in_data_valid)
        `BR_UNUSED(in_data)
        `BR_TIEOFF_ZERO(internal_out_data_valid)
        `BR_TIEOFF_ZERO(internal_out_data)
      end

    end else begin : gen_compare_impl
      // If Depth is not a power-of-2 we cannot just slice off the MSBs for the tile select.
      // We have to look at the address range and steer it with bit overlaps.
      for (genvar i = 0; i < Tiles; i++) begin : gen_compare
        // inclusive
        localparam logic [InputAddressWidth-1:0] TileBaseAddress = TileDepth * i;
        // exclusive
        localparam logic [InputAddressWidth-1:0] TileBoundAddress = TileDepth * (i + 1);
        // ri lint_check_waive INEFFECTIVE_NET
        logic [InputAddressWidth-1:0] tile_addr_offset;
        logic in_addr_in_range;

        // ri lint_check_waive ARITH_EXTENSION
        assign tile_addr_offset = (in_addr - TileBaseAddress);

        assign in_addr_in_range = in_valid &&
            // Lint waiver needed because when i == 0, this subexpression is always true.
            // ri lint_check_waive INVALID_COMPARE
            (in_addr >= TileBaseAddress) && (in_addr < TileBoundAddress);
        assign internal_out_addr[i] = tile_addr_offset[OutputAddressWidth-1:0];
        assign internal_out_valid[i] = in_valid && in_addr_in_range;

        `BR_UNUSED_NAMED(tile_addr_offset_msbs,
                         tile_addr_offset[InputAddressWidth-1:OutputAddressWidth])

        if (EnableDatapath) begin : gen_datapath
          assign internal_out_data_valid[i] = in_data_valid && in_addr_in_range;
          assign internal_out_data[i] = in_data;
        end else begin : gen_no_datapath
          `BR_UNUSED(in_data_valid)
          `BR_UNUSED(in_data)
          `BR_TIEOFF_ZERO_NAMED(internal_out_data_valid_i, internal_out_data_valid[i])
          `BR_TIEOFF_ZERO_NAMED(internal_out_data_i, internal_out_data[i])
        end
      end
    end

    // Replicate to reduce register fanout when Stages >= 1
    for (genvar i = 0; i < Tiles; i++) begin : gen_out
      br_delay_valid #(
          .Width(OutputAddressWidth),
          .NumStages(Stages),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_delay_valid_addr (
          .clk,
          .rst,
          .in_valid(internal_out_valid[i]),
          .in(internal_out_addr[i]),
          .out_valid(out_valid[i]),
          .out(out_addr[i]),
          .out_valid_stages(),  // unused
          .out_stages()  // unused
      );

      if (EnableDatapath) begin : gen_datapath
        br_delay_valid #(
            .Width(DataWidth),
            .NumStages(Stages),
            .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
        ) br_delay_valid_data (
            .clk,
            .rst,
            .in_valid(internal_out_data_valid[i]),
            .in(internal_out_data[i]),
            .out_valid(out_data_valid[i]),
            .out(out_data[i]),
            .out_valid_stages(),  // unused
            .out_stages()  // unused
        );
      end else begin : gen_no_datapath
        `BR_UNUSED_NAMED(internal_out_data_valid_i, internal_out_data_valid[i])
        `BR_UNUSED_NAMED(internal_out_data_i, internal_out_data[i])
        `BR_TIEOFF_ZERO_NAMED(out_data_valid_i, out_data_valid[i])
        `BR_TIEOFF_ZERO_NAMED(out_data_i, out_data[i])
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(out_valid_onehot0_a, $onehot0(out_valid))

  for (genvar i = 0; i < Tiles; i++) begin : gen_out_checks
    `BR_ASSERT_IMPL(out_addr_in_range_a, out_valid[i] |-> out_addr[i] < TileDepth)
    if (EnableDatapath) begin : gen_datapath_checks_impl
      `BR_ASSERT_IMPL(out_data_valid_iff_out_valid_a, out_data_valid[i] |-> out_valid[i])
    end else begin : gen_no_datapath_checks_impl
      `BR_ASSERT_IMPL(out_data_valid_tied_to_0_a, out_data_valid[i] == 0)
    end
  end

  if (Stages > 0) begin : gen_impl_checks_delayed
    `BR_ASSERT_IMPL(valid_propagation_a, in_valid |-> ##Stages $onehot(out_valid))
    for (genvar i = 0; i < Tiles; i++) begin : gen_tiles_check
      `BR_ASSERT_IMPL(out_addr_correct_a,
                      out_valid[i] |-> $past(
                          in_valid, Stages
                      ) && (out_addr[i] == $past(
                          (in_addr - (TileDepth * i)), Stages
                      )))
    end
  end else begin : gen_impl_checks_not_delayed
    `BR_ASSERT_IMPL(valid_propagation_a, in_valid |-> $onehot(out_valid))
    for (genvar i = 0; i < Tiles; i++) begin : gen_tiles_check
      `BR_ASSERT_IMPL(out_addr_correct_a,
                      out_valid[i] |-> in_valid && (out_addr[i] == (in_addr - (TileDepth * i))))
    end
  end

endmodule : br_ram_addr_decoder
