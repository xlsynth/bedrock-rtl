// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flop FIFO With Unstable Push Interface
//
// Accepts valid and data that may change or be revoked while push_ready is low, then presents a
// stable ready-valid pop interface. Combinational push-to-pop bypass is disabled so unstable input
// signals cannot propagate to the pop interface.

`include "br_asserts.svh"

module br_fifo_flops_unstable #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, ensure pop_valid/pop_data always come directly from a register.
    parameter bit RegisterPopOutputs = 0,
    // Number of tiles in the depth dimension. Must be at least 1.
    parameter int FlopRamDepthTiles = 1,
    // Number of tiles in the width dimension. Must be at least 1 and evenly divide Width.
    parameter int FlopRamWidthTiles = 1,
    // Number of pipeline stages along the RAM write-address and read-address paths.
    parameter int FlopRamAddressDepthStages = 0,
    // Number of pipeline stages along the RAM read-data path in the depth dimension.
    parameter int FlopRamReadDataDepthStages = 0,
    // Number of pipeline stages along the RAM read-data path in the width dimension.
    parameter int FlopRamReadDataWidthStages = 0,
    // If 1, cover push-side backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_data_unstable is known whenever push_valid_unstable is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, assert that the FIFO is empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,

    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    output logic             push_ready,
    input  logic             push_valid_unstable,
    input  logic [Width-1:0] push_data_unstable,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    output logic                  empty,
    output logic                  empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next
);

  localparam int RamReadLatency =
      FlopRamAddressDepthStages + FlopRamReadDataDepthStages + FlopRamReadDataWidthStages;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(depth_must_be_at_least_two_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(flop_ram_depth_tiles_must_be_at_least_one_a, FlopRamDepthTiles >= 1)
  `BR_ASSERT_STATIC(flop_ram_width_tiles_must_be_at_least_one_a, FlopRamWidthTiles >= 1)
  if (FlopRamWidthTiles >= 1) begin : gen_flop_ram_width_tiles_divisibility_check
    `BR_ASSERT_STATIC(flop_ram_width_tiles_must_evenly_divide_width_a,
                      (Width % FlopRamWidthTiles) == 0)
  end
  `BR_ASSERT_STATIC(flop_ram_address_depth_stages_must_be_nonnegative_a,
                    FlopRamAddressDepthStages >= 0)
  `BR_ASSERT_STATIC(flop_ram_read_data_depth_stages_must_be_nonnegative_a,
                    FlopRamReadDataDepthStages >= 0)
  `BR_ASSERT_STATIC(flop_ram_read_data_width_stages_must_be_nonnegative_a,
                    FlopRamReadDataWidthStages >= 0)
  `BR_ASSERT_STATIC(depth_must_exceed_ram_read_latency_a, Depth > (RamReadLatency + 1))

  // Rely on submodule integration checks.

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(1'b0),
      .RegisterPopOutputs(RegisterPopOutputs),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(1'b0),
      .EnableAssertPushDataStability(1'b0),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
  ) br_fifo_flops (
      .clk,
      .rst,
      .push_ready,
      .push_valid(push_valid_unstable),
      .push_data (push_data_unstable),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .empty,
      .empty_next,
      .items,
      .items_next
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks.

endmodule : br_fifo_flops_unstable
