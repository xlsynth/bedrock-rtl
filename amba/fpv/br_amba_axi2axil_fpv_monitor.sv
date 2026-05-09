// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4 to AXI4-Lite Bridge FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi2axil_fpv_monitor #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int IdWidth = 4,
    parameter int AWUserWidth = 8,
    parameter int ARUserWidth = 8,
    parameter int WUserWidth = 8,
    parameter int BUserWidth = 8,
    parameter int RUserWidth = 8,
    parameter int MaxOutstandingReqs = 16,
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input logic [                 AddrWidth-1:0] axi_awaddr,
    input logic [                   IdWidth-1:0] axi_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] axi_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] axi_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] axi_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] axi_awprot,
    input logic [               AWUserWidth-1:0] axi_awuser,
    input logic                                  axi_awvalid,
    input logic                                  axi_awready,
    input logic [                 DataWidth-1:0] axi_wdata,
    input logic [               StrobeWidth-1:0] axi_wstrb,
    input logic [                WUserWidth-1:0] axi_wuser,
    input logic                                  axi_wlast,
    input logic                                  axi_wvalid,
    input logic                                  axi_wready,
    input logic [                   IdWidth-1:0] axi_bid,
    input logic [                BUserWidth-1:0] axi_buser,
    input logic [     br_amba::AxiRespWidth-1:0] axi_bresp,
    input logic                                  axi_bvalid,
    input logic                                  axi_bready,
    input logic [                 AddrWidth-1:0] axi_araddr,
    input logic [                   IdWidth-1:0] axi_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] axi_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] axi_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] axi_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] axi_arprot,
    input logic [               ARUserWidth-1:0] axi_aruser,
    input logic                                  axi_arvalid,
    input logic                                  axi_arready,
    input logic [                   IdWidth-1:0] axi_rid,
    input logic [                 DataWidth-1:0] axi_rdata,
    input logic [                RUserWidth-1:0] axi_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] axi_rresp,
    input logic                                  axi_rlast,
    input logic                                  axi_rvalid,
    input logic                                  axi_rready,

    // AXI4-Lite interface
    input logic [            AddrWidth-1:0] axil_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input logic [          AWUserWidth-1:0] axil_awuser,
    input logic                             axil_awvalid,
    input logic                             axil_awready,
    input logic [            DataWidth-1:0] axil_wdata,
    input logic [          StrobeWidth-1:0] axil_wstrb,
    input logic [           WUserWidth-1:0] axil_wuser,
    input logic                             axil_wvalid,
    input logic                             axil_wready,
    input logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input logic [           BUserWidth-1:0] axil_buser,
    input logic                             axil_bvalid,
    input logic                             axil_bready,
    input logic [            AddrWidth-1:0] axil_araddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    input logic [          ARUserWidth-1:0] axil_aruser,
    input logic                             axil_arvalid,
    input logic                             axil_arready,
    input logic [            DataWidth-1:0] axil_rdata,
    input logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    input logic [           RUserWidth-1:0] axil_ruser,
    input logic                             axil_rvalid,
    input logic                             axil_rready
);

  // ABVIP should send more than DUT to test backpressure
  localparam int MaxPending = MaxOutstandingReqs + 2;
  localparam int FvSplitCountWidth = br_amba::AxiBurstLenWidth + 1;
  localparam int FvAwReqPayloadWidth = AddrWidth + br_amba::AxiBurstLenWidth +
      br_amba::AxiBurstSizeWidth + br_amba::AxiBurstTypeWidth + br_amba::AxiProtWidth + AWUserWidth;
  localparam int FvArReqPayloadWidth = AddrWidth + br_amba::AxiBurstLenWidth +
      br_amba::AxiBurstSizeWidth + br_amba::AxiBurstTypeWidth + br_amba::AxiProtWidth + ARUserWidth;

  // Predict the AXI-Lite address for a split beat from one AXI burst.
  // INCR keeps the original address on beat 0, then aligns later beats to the
  // transfer size. WRAP applies the wrap boundary. FIXED keeps the start
  // address for every beat.
  function automatic logic [AddrWidth-1:0] fv_axil_addr(
      input logic [AddrWidth-1:0] start_addr, input logic [br_amba::AxiBurstSizeWidth-1:0] size,
      input logic [br_amba::AxiBurstLenWidth-1:0] burst_len,
      input logic [br_amba::AxiBurstTypeWidth-1:0] burst_type,
      input logic [br_amba::AxiBurstLenWidth-1:0] index);
    logic [AddrWidth-1:0] incr_addr;
    logic [AddrWidth-1:0] wrap_base_addr;
    logic [AddrWidth-1:0] wrap_mask;
    logic [AddrWidth-1:0] align_mask;

    incr_addr = start_addr + (index << size);

    unique case (br_amba::axi_burst_type_t'(burst_type))
      br_amba::AxiBurstIncr: begin
        align_mask   = {AddrWidth{1'b1}} << size;
        fv_axil_addr = (index == 'd0) ? start_addr : (incr_addr & align_mask);
      end
      br_amba::AxiBurstWrap: begin
        wrap_mask = ((burst_len + 1'b1) << size) - 1'b1;
        wrap_base_addr = start_addr & ~wrap_mask;
        fv_axil_addr = wrap_base_addr | (incr_addr & wrap_mask);
      end
      default: begin
        fv_axil_addr = start_addr;
      end
    endcase
  endfunction

  function automatic logic fv_unaligned_addr(input logic [AddrWidth-1:0] addr,
                                             input logic [br_amba::AxiBurstSizeWidth-1:0] size);
    logic [AddrWidth-1:0] mask;

    mask = (AddrWidth'(1'b1) << size) - 1'b1;
    fv_unaligned_addr = |(addr & mask);
  endfunction

  // Track split AXI-Lite B responses for each AXI write burst and check that
  // the public AXI B response reports the first non-OKAY split response.
  logic axi_aw_handshake;
  logic axi_ar_handshake;
  logic axil_aw_handshake;
  logic axil_ar_handshake;
  logic axil_b_handshake;
  logic fv_awlen_fifo_push_ready;
  logic fv_awlen_fifo_pop_ready;
  logic fv_awlen_fifo_pop_valid;
  logic fv_awlen_fifo_empty;
  logic fv_awlen_fifo_full;
  logic [FvSplitCountWidth-1:0] fv_awlen_fifo_push_data;
  logic [FvSplitCountWidth-1:0] fv_awlen_fifo_pop_data;
  logic fv_b_active;
  logic fv_b_active_next;
  logic [FvSplitCountWidth-1:0] fv_b_split_count;
  logic [FvSplitCountWidth-1:0] fv_b_remaining;
  logic [FvSplitCountWidth-1:0] fv_b_remaining_next;
  logic [br_amba::AxiRespWidth-1:0] fv_bresp;
  logic [br_amba::AxiRespWidth-1:0] fv_bresp_after_axil;
  logic [br_amba::AxiRespWidth-1:0] fv_bresp_next;
  logic fv_axil_b_final;

  assign axi_aw_handshake = axi_awvalid && axi_awready;
  assign axi_ar_handshake = axi_arvalid && axi_arready;
  assign axil_aw_handshake = axil_awvalid && axil_awready;
  assign axil_ar_handshake = axil_arvalid && axil_arready;
  assign axil_b_handshake = axil_bvalid && axil_bready;
  assign fv_awlen_fifo_push_ready = !fv_awlen_fifo_full;
  assign fv_awlen_fifo_pop_valid = !fv_awlen_fifo_empty || axi_aw_handshake;
  assign fv_awlen_fifo_push_data = FvSplitCountWidth'(axi_awlen) + FvSplitCountWidth'(1'b1);
  assign fv_awlen_fifo_pop_ready = axil_b_handshake && !fv_b_active;
  assign fv_b_split_count = fv_b_active ? fv_b_remaining : fv_awlen_fifo_pop_data;
  assign fv_bresp_after_axil =
      ((fv_bresp == br_amba::AxiRespOkay) && (axil_bresp != br_amba::AxiRespOkay)) ?
      axil_bresp : fv_bresp;
  assign fv_axil_b_final =
      axil_bvalid && (fv_b_active ? (fv_b_remaining == FvSplitCountWidth'(1'b1)) :
                      (fv_awlen_fifo_pop_valid &&
                       (fv_awlen_fifo_pop_data == FvSplitCountWidth'(1'b1))));

  // Update the expected aggregate B response after each split AXI-Lite B
  // handshake. The saved response changes only for the first non-OKAY response
  // and resets after the final split response for the AXI burst.
  always_comb begin
    fv_b_active_next = fv_b_active;
    fv_b_remaining_next = fv_b_remaining;
    fv_bresp_next = fv_bresp;

    if (axil_b_handshake) begin
      if (fv_b_split_count == FvSplitCountWidth'(1'b1)) begin
        fv_b_active_next = 1'b0;
        fv_b_remaining_next = '0;
        fv_bresp_next = br_amba::AxiRespOkay;
      end else begin
        fv_b_active_next = 1'b1;
        fv_b_remaining_next = fv_b_split_count - FvSplitCountWidth'(1'b1);
        fv_bresp_next = fv_bresp_after_axil;
      end
    end
  end

  `BR_REGLI(fv_b_active, fv_b_active_next, axil_b_handshake, 1'b0)
  `BR_REGLI(fv_b_remaining, fv_b_remaining_next, axil_b_handshake, '0)
  `BR_REGLI(fv_bresp, fv_bresp_next, axil_b_handshake, br_amba::AxiRespOkay)

  // Queue the number of expected split AXI-Lite B responses for each accepted
  // AXI AW request. Bypass lets the first B response consume a same-cycle AW.
  fv_fifo #(
      .Depth(MaxOutstandingReqs),
      .DataWidth(FvSplitCountWidth),
      .Bypass(1)
  ) fv_awlen_fifo (
      .clk,
      .rst,

      .push(axi_aw_handshake),
      .push_data(fv_awlen_fifo_push_data),

      .pop(fv_awlen_fifo_pop_ready),
      .pop_data(fv_awlen_fifo_pop_data),
      .empty(fv_awlen_fifo_empty),
      .full(fv_awlen_fifo_full)
  );

  // The FV AW-length queue should have space whenever the DUT accepts an AW.
  `BR_ASSERT(awlen_fifo_ready_a, axi_aw_handshake |-> fv_awlen_fifo_push_ready)

  // A first split B response must have a matching accepted AW burst length.
  `BR_ASSERT(axil_b_has_aw_a, axil_bvalid && !fv_b_active |-> fv_awlen_fifo_pop_valid)

  // On the final split B response, the public AXI B response must match the
  // first non-OKAY response observed across the split AXI-Lite responses.
  `BR_ASSERT(aggregated_bresp_a,
             fv_axil_b_final && axi_bvalid |-> (axi_bresp == fv_bresp_after_axil))

  // The bridge must present the public AXI B response when the final split
  // AXI-Lite B response for the burst is available.
  `BR_ASSERT(final_axil_b_drives_axi_b_a, fv_axil_b_final |-> axi_bvalid)

  // Predict the split AXI-Lite AW/AR requests for each accepted AXI burst. This
  // covers narrow bursts by stepping at 2**AxSIZE, and unaligned INCR bursts by
  // passing the first beat address through before aligning subsequent beats.
  logic fv_aw_req_fifo_pop_ready;
  logic fv_aw_req_fifo_empty;
  logic fv_aw_req_fifo_full;
  logic fv_aw_req_valid;
  logic [FvAwReqPayloadWidth-1:0] fv_aw_req_fifo_push_data;
  logic [FvAwReqPayloadWidth-1:0] fv_aw_req_fifo_pop_data;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_aw_req_index;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_aw_req_index_next;
  logic [AddrWidth-1:0] fv_awaddr;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_awlen;
  logic [br_amba::AxiBurstSizeWidth-1:0] fv_awsize;
  logic [br_amba::AxiBurstTypeWidth-1:0] fv_awburst;
  logic [br_amba::AxiProtWidth-1:0] fv_awprot;
  logic [AWUserWidth-1:0] fv_awuser;
  logic [AddrWidth-1:0] fv_expected_axil_awaddr;
  logic fv_axil_aw_last;

  logic fv_ar_req_fifo_pop_ready;
  logic fv_ar_req_fifo_empty;
  logic fv_ar_req_fifo_full;
  logic fv_ar_req_valid;
  logic [FvArReqPayloadWidth-1:0] fv_ar_req_fifo_push_data;
  logic [FvArReqPayloadWidth-1:0] fv_ar_req_fifo_pop_data;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_ar_req_index;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_ar_req_index_next;
  logic [AddrWidth-1:0] fv_araddr;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_arlen;
  logic [br_amba::AxiBurstSizeWidth-1:0] fv_arsize;
  logic [br_amba::AxiBurstTypeWidth-1:0] fv_arburst;
  logic [br_amba::AxiProtWidth-1:0] fv_arprot;
  logic [ARUserWidth-1:0] fv_aruser;
  logic [AddrWidth-1:0] fv_expected_axil_araddr;
  logic fv_axil_ar_last;

  assign fv_aw_req_fifo_push_data = {
    axi_awaddr, axi_awlen, axi_awsize, axi_awburst, axi_awprot, axi_awuser
  };
  assign {fv_awaddr, fv_awlen, fv_awsize, fv_awburst, fv_awprot, fv_awuser} =
      fv_aw_req_fifo_pop_data;
  assign fv_aw_req_valid = !fv_aw_req_fifo_empty || axi_aw_handshake;
  assign fv_expected_axil_awaddr = fv_axil_addr(
      fv_awaddr, fv_awsize, fv_awlen, fv_awburst, fv_aw_req_index
  );
  assign fv_axil_aw_last = fv_aw_req_index == fv_awlen;
  assign fv_aw_req_fifo_pop_ready = axil_aw_handshake && fv_axil_aw_last;
  assign fv_aw_req_index_next = fv_axil_aw_last ? '0 : fv_aw_req_index + 1'b1;

  fv_fifo #(
      .Depth(MaxOutstandingReqs),
      .DataWidth(FvAwReqPayloadWidth),
      .Bypass(1)
  ) fv_aw_req_fifo (
      .clk,
      .rst,

      .push(axi_aw_handshake),
      .push_data(fv_aw_req_fifo_push_data),

      .pop(fv_aw_req_fifo_pop_ready),
      .pop_data(fv_aw_req_fifo_pop_data),
      .empty(fv_aw_req_fifo_empty),
      .full(fv_aw_req_fifo_full)
  );

  `BR_REGLI(fv_aw_req_index, fv_aw_req_index_next, axil_aw_handshake, '0)

  // The write-side prediction FIFO must have space whenever the DUT accepts a
  // new AXI AW request, unless the same cycle consumes the final predicted beat.
  `BR_ASSERT(aw_req_fifo_ready_a,
             axi_aw_handshake |-> (!fv_aw_req_fifo_full || fv_aw_req_fifo_pop_ready))

  // Every AXI-Lite AW produced by the DUT must correspond to an accepted AXI AW
  // burst currently tracked by the prediction model.
  `BR_ASSERT(axil_aw_has_axi_aw_a, axil_awvalid |-> fv_aw_req_valid)

  // Check the split AXI-Lite AW payload against the predicted burst beat. The
  // address calculation is where narrow and unaligned burst behavior is verified.
  /* verilog_format: off */
  `BR_ASSERT(
      axil_aw_payload_a,
      axil_awvalid |-> ({axil_awaddr, axil_awprot, axil_awuser} ==
                        {fv_expected_axil_awaddr, fv_awprot, fv_awuser}))
  /* verilog_format: on */
  assign fv_ar_req_fifo_push_data = {
    axi_araddr, axi_arlen, axi_arsize, axi_arburst, axi_arprot, axi_aruser
  };
  assign {fv_araddr, fv_arlen, fv_arsize, fv_arburst, fv_arprot, fv_aruser} =
      fv_ar_req_fifo_pop_data;
  assign fv_ar_req_valid = !fv_ar_req_fifo_empty || axi_ar_handshake;
  assign fv_expected_axil_araddr = fv_axil_addr(
      fv_araddr, fv_arsize, fv_arlen, fv_arburst, fv_ar_req_index
  );
  assign fv_axil_ar_last = fv_ar_req_index == fv_arlen;
  assign fv_ar_req_fifo_pop_ready = axil_ar_handshake && fv_axil_ar_last;
  assign fv_ar_req_index_next = fv_axil_ar_last ? '0 : fv_ar_req_index + 1'b1;

  fv_fifo #(
      .Depth(MaxOutstandingReqs),
      .DataWidth(FvArReqPayloadWidth),
      .Bypass(1)
  ) fv_ar_req_fifo (
      .clk,
      .rst,

      .push(axi_ar_handshake),
      .push_data(fv_ar_req_fifo_push_data),

      .pop(fv_ar_req_fifo_pop_ready),
      .pop_data(fv_ar_req_fifo_pop_data),
      .empty(fv_ar_req_fifo_empty),
      .full(fv_ar_req_fifo_full)
  );

  `BR_REGLI(fv_ar_req_index, fv_ar_req_index_next, axil_ar_handshake, '0)

  // The read-side prediction FIFO must have space whenever the DUT accepts a
  // new AXI AR request, unless the same cycle consumes the final predicted beat.
  `BR_ASSERT(ar_req_fifo_ready_a,
             axi_ar_handshake |-> (!fv_ar_req_fifo_full || fv_ar_req_fifo_pop_ready))

  // Every AXI-Lite AR produced by the DUT must correspond to an accepted AXI AR
  // burst currently tracked by the prediction model.
  `BR_ASSERT(axil_ar_has_axi_ar_a, axil_arvalid |-> fv_ar_req_valid)

  // Check the split AXI-Lite AR payload against the predicted burst beat. The
  // address calculation is where narrow and unaligned burst behavior is verified.
  /* verilog_format: off */
  `BR_ASSERT(
      axil_ar_payload_a,
      axil_arvalid |-> ({axil_araddr, axil_arprot, axil_aruser} ==
                        {fv_expected_axil_araddr, fv_arprot, fv_aruser}))
  /* verilog_format: on */

  // Cover the newly supported multi-beat narrow bursts so the formal run shows
  // the assumptions no longer exclude them.
  `BR_COVER(narrow_write_burst_c, axi_aw_handshake && (axi_awsize < $clog2(StrobeWidth)
            ) && (axi_awlen != '0))
  `BR_COVER(narrow_read_burst_c, axi_ar_handshake && (axi_arsize < $clog2(StrobeWidth)
            ) && (axi_arlen != '0))

  // Cover unaligned INCR bursts, where the first split request keeps the
  // original unaligned address and later requests align to the transfer size.
  `BR_COVER(unaligned_incr_write_burst_c,
            axi_aw_handshake && (axi_awburst == br_amba::AxiBurstIncr) && fv_unaligned_addr(
            axi_awaddr, axi_awsize) && (axi_awlen != '0))
  `BR_COVER(unaligned_incr_read_burst_c,
            axi_ar_handshake && (axi_arburst == br_amba::AxiBurstIncr) && fv_unaligned_addr(
            axi_araddr, axi_arsize) && (axi_arlen != '0))

  // Cover unaligned FIXED bursts, where every split request should keep the
  // original address unchanged.
  `BR_COVER(unaligned_fixed_write_burst_c,
            axi_aw_handshake && (axi_awburst == br_amba::AxiBurstFixed) && fv_unaligned_addr(
            axi_awaddr, axi_awsize) && (axi_awlen != '0))
  `BR_COVER(unaligned_fixed_read_burst_c,
            axi_ar_handshake && (axi_arburst == br_amba::AxiBurstFixed) && fv_unaligned_addr(
            axi_araddr, axi_arsize) && (axi_arlen != '0))

  // Instance of the AXI Slave DUV
  axi4_master #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      // when there is no valid, ready doesn't have to be high eventually
      // This will only turn off assertion without precondition: `STRENGTH(##[0:$] arready
      // (arvalid && !arready) |=> `STRENGTH(##[0:$] arready) is still enabled
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) axi4 (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (axi_awvalid),
      .awready (axi_awready),
      .awid    (axi_awid),
      .awaddr  (axi_awaddr),
      .awlen   (axi_awlen),
      .awsize  (axi_awsize),
      .awburst (axi_awburst),
      .awuser  (axi_awuser),
      .awprot  (axi_awprot),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (axi_wvalid),
      .wready  (axi_wready),
      .wdata   (axi_wdata),
      .wstrb   (axi_wstrb),
      .wlast   (axi_wlast),
      .wuser   (axi_wuser),
      // Write Response channel
      .bvalid  (axi_bvalid),
      .bready  (axi_bready),
      .bid     (axi_bid),
      .bresp   (axi_bresp),
      .buser   (axi_buser),
      // Read Address Channel
      .arvalid (axi_arvalid),
      .arready (axi_arready),
      .arid    (axi_arid),
      .araddr  (axi_araddr),
      .arlen   (axi_arlen),
      .arsize  (axi_arsize),
      .arburst (axi_arburst),
      .aruser  (axi_aruser),
      .arprot  (axi_arprot),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (axi_rvalid),
      .rready  (axi_rready),
      .ruser   (axi_ruser),
      .rid     (axi_rid),
      .rdata   (axi_rdata),
      .rresp   (axi_rresp),
      .rlast   (axi_rlast)
  );

  // AXI4-Lite interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      // when there is no valid, ready doesn't have to be high eventually
      // This will only turn off assertion without precondition: `STRENGTH(##[0:$] arready
      // (arvalid && !arready) |=> `STRENGTH(##[0:$] arready) is still enabled
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) axi4_lite (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (axil_awvalid),
      .awready (axil_awready),
      .awuser  (axil_awuser),
      .awaddr  (axil_awaddr),
      .awprot  (axil_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (axil_wvalid),
      .wready  (axil_wready),
      .wuser   (axil_wuser),
      .wdata   (axil_wdata),
      .wstrb   (axil_wstrb),
      .wlast   (),
      // Write Response channel
      .bvalid  (axil_bvalid),
      .bready  (axil_bready),
      .buser   (axil_buser),
      .bresp   (axil_bresp),
      .bid     (),
      // Read Address Channel
      .arvalid (axil_arvalid),
      .arready (axil_arready),
      .araddr  (axil_araddr),
      .aruser  (axil_aruser),
      .arprot  (axil_arprot),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (axil_rvalid),
      .rready  (axil_rready),
      .ruser   (axil_ruser),
      .rdata   (axil_rdata),
      .rresp   (axil_rresp),
      .rid     (),
      .rlast   ()
  );

endmodule : br_amba_axi2axil_fpv_monitor

bind br_amba_axi2axil br_amba_axi2axil_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth(WUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .MaxOutstandingReqs(MaxOutstandingReqs)
) monitor (.*);
