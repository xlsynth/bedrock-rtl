// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4-Lite MSI Generator

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_msi_fpv_monitor #(
    parameter int AddrWidth = 40,  // must be at least 12
    parameter int DataWidth = 64,  // must be 32 or 64
    parameter int NumInterrupts = 2,  // must be at least 2
    parameter int NumMsiDestAddr = 1,  // must be at least 1
    parameter int DeviceIdWidth = 16,  // must be less than or equal to AddrWidth
    parameter int EventIdWidth = 16,  // must be less than or equal to DataWidth
    parameter int ThrottleCntrWidth = 16,  // must be at least 1
    localparam int MsiDstIdxWidth = (NumMsiDestAddr > 1) ? $clog2(NumMsiDestAddr) : 1,
    localparam int StrobeWidth = (DataWidth + 7) / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Interrupt inputs
    input logic [NumInterrupts-1:0] irq,

    // MSI Configuration
    input logic [NumMsiDestAddr-1:0][AddrWidth-1:0] msi_dest_addr,
    input logic [NumInterrupts-1:0] msi_enable,
    input logic [NumInterrupts-1:0][MsiDstIdxWidth-1:0] msi_dest_idx,
    input logic [NumInterrupts-1:0][DeviceIdWidth-1:0] device_id_per_irq,
    input logic [NumInterrupts-1:0][EventIdWidth-1:0] event_id_per_irq,

    // Throttle configuration
    input logic throttle_en,
    input logic [ThrottleCntrWidth-1:0] throttle_cntr_threshold,

    // Error output
    input logic error,

    // AXI4-Lite write-only initiator interface
    input logic [            AddrWidth-1:0] init_awaddr,
    input logic                             init_awvalid,
    input logic                             init_awready,
    input logic [            DataWidth-1:0] init_wdata,
    input logic [          StrobeWidth-1:0] init_wstrb,
    input logic                             init_wvalid,
    input logic                             init_wready,
    input logic [br_amba::AxiRespWidth-1:0] init_bresp,
    input logic                             init_bvalid,
    input logic                             init_bready
);

  // ----------FV assumptions----------
  `BR_ASSUME(throttle_en_stable_a, $stable(throttle_en))
  `BR_ASSUME(throttle_cntr_stable_a, $stable(throttle_cntr_threshold)
             && throttle_cntr_threshold != 'd0)
  `BR_ASSUME(msi_enable_stable_a, $stable(msi_enable))
  `BR_ASSUME(msi_dest_addr_stable_a, $stable(msi_dest_addr))
  `BR_ASSUME(msi_dest_idx_stable_a, $stable(msi_dest_idx))
  `BR_ASSUME(device_id_stable_a, $stable(device_id_per_irq))
  `BR_ASSUME(event_id_stable_a, $stable(event_id_per_irq))
  for (genvar i = 0; i < NumInterrupts; i++) begin : gen_id
    `BR_ASSUME(msi_dest_idx_in_range_a, msi_dest_idx[i] < NumMsiDestAddr)
  end

  // ----------FV assertions----------
  localparam int AddrWidthPadding = (AddrWidth - DeviceIdWidth) - 2;
  localparam int EventIdPadding = 32 - EventIdWidth;
  localparam int DataWidthPadding = DataWidth - 32;
  localparam int EventIdStrobeWidth = 4;
  localparam int StrobeWidthPadding = StrobeWidth - EventIdStrobeWidth;
  localparam int StrobeBitWidth = $clog2(StrobeWidth);

  logic [AddrWidth-1:0] msi_base_addr;
  logic [NumInterrupts-1:0][AddrWidth-1:0] fv_init_awaddr;
  logic [NumInterrupts-1:0][DataWidth-1:0] fv_init_wdata;
  logic [NumInterrupts-1:0][StrobeWidth-1:0] fv_init_wstrb;
  logic awaddr_match;
  logic wdata_match;
  logic wstrb_match;

  always_comb begin
    for (int i = 0; i < NumInterrupts; i++) begin
      msi_base_addr = msi_dest_addr[msi_dest_idx[i]];
      fv_init_awaddr[i] = msi_base_addr + {{AddrWidthPadding{1'b0}}, device_id_per_irq[i], 2'b00};
      if (StrobeWidthPadding == 0) begin
        fv_init_wdata[i] = {{EventIdPadding{1'b0}}, event_id_per_irq[i]};
        fv_init_wstrb[i] = {EventIdStrobeWidth{1'b1}};
      end else if (device_id_per_irq[i][0]) begin
        fv_init_wdata[i] = {{EventIdPadding{1'b0}}, event_id_per_irq[i], {DataWidthPadding{1'b0}}};
        fv_init_wstrb[i] = {{EventIdStrobeWidth{1'b1}}, {StrobeWidthPadding{1'b0}}};
      end else begin
        fv_init_wdata[i] = {{DataWidthPadding{1'b0}}, {EventIdPadding{1'b0}}, event_id_per_irq[i]};
        fv_init_wstrb[i] = {{StrobeWidthPadding{1'b0}}, {EventIdStrobeWidth{1'b1}}};
      end
      for (int j = 0; j < StrobeWidth; j++) begin : gen_asm
        // if index is not address[StrobeBitWidth-1:0], wstrb must be 0
        // e.g. if StrobeWidth=8, then StrobeBitWidth=3
        // if awaddr[2:0] == 3'b010, then only wstrb[2] can be 1, others must be 0
        if (j != fv_init_awaddr[i][StrobeBitWidth-1:0]) begin
          `BR_ASSUME(legal_narrow_access_a, fv_init_wstrb[i][j] == 1'b0)
        end
      end
    end
  end

  // There is no 1-to-1 correspondence bwteen irq and AXI interface.
  // irq can drop before it's sent out at AXI interface.
  // as long as AXI won't send out spurious payload, it's fine
  always_comb begin
    awaddr_match = 1'b0;
    wdata_match  = 1'b0;
    wstrb_match  = 1'b0;
    for (int i = 0; i < NumInterrupts; i++) begin
      if (init_awvalid && (init_awaddr == fv_init_awaddr[i])) begin
        awaddr_match = 1'b1;
      end
      if (init_wvalid && (init_wdata == fv_init_wdata[i])) begin
        wdata_match = 1'b1;
      end
      if (init_wvalid && (init_wstrb == fv_init_wstrb[i])) begin
        wstrb_match = 1'b1;
      end
    end
  end

  // device_id/event_id encoding check
  `BR_ASSERT(awaddr_match_a, init_awvalid |-> awaddr_match)
  `BR_ASSERT(wdata_match_a, init_wvalid |-> wdata_match)
  `BR_ASSERT(wstrb_match_a, init_wvalid |-> wstrb_match)

  // throttle check
  logic [ThrottleCntrWidth-1:0] aw_throttle_cntr;
  logic [ThrottleCntrWidth-1:0] w_throttle_cntr;
  logic aw_in_progress;
  logic w_in_progress;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      aw_throttle_cntr <= 'd0;
    end else begin
      if ($rose(init_awvalid) & throttle_en) begin
        aw_throttle_cntr <= throttle_cntr_threshold - 'd1;
      end else begin
        aw_throttle_cntr <= aw_throttle_cntr != 'd0 ? aw_throttle_cntr - 'd1 : 'd0;
      end
    end
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      w_throttle_cntr <= 'd0;
    end else begin
      if ($rose(init_wvalid) & throttle_en) begin
        w_throttle_cntr <= throttle_cntr_threshold - 'd1;
      end else begin
        w_throttle_cntr <= w_throttle_cntr != 'd0 ? w_throttle_cntr - 'd1 : 'd0;
      end
    end
  end

  assign aw_in_progress = aw_throttle_cntr != 'd0;
  assign w_in_progress  = w_throttle_cntr != 'd0;

  `BR_ASSERT(awvalid_throttle_a, aw_in_progress |-> !$rose(init_awvalid))
  `BR_ASSERT(wvalid_throttle_a, w_in_progress |-> !$rose(init_wvalid))

  // AXI4-Lite write-only initiator interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) axi (
      // Global signals
      .aclk   (clk),
      .aresetn(!rst),
      .csysreq(1'b1),
      .csysack(1'b1),
      .cactive(1'b1),
      // Write Address Channel
      .awvalid(init_awvalid),
      .awready(init_awready),
      .awaddr (init_awaddr),
      .awprot ('d0),
      // Write Channel
      .wvalid (init_wvalid),
      .wready (init_wready),
      .wdata  (init_wdata),
      .wstrb  (init_wstrb),
      // Write Response channel
      .bvalid (init_bvalid),
      .bready (init_bready),
      .bresp  (init_bresp),
      // Read Address Channel
      .arvalid('d0),
      .arready('d0),
      // Read Channel
      .rvalid ('d0),
      .rready ('d0)
  );

endmodule : br_amba_axil_msi_fpv_monitor

bind br_amba_axil_msi br_amba_axil_msi_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .NumInterrupts(NumInterrupts),
    .NumMsiDestAddr(NumMsiDestAddr),
    .DeviceIdWidth(DeviceIdWidth),
    .EventIdWidth(EventIdWidth),
    .ThrottleCntrWidth(ThrottleCntrWidth)
) monitor (.*);
