// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL CSR Demux Select-Onehot FPV Monitor
//
// This checker verifies br_csr_demux_select_onehot independent of address
// decoding. It checks that a onehot-selected upstream request reaches the
// selected downstream with its payload intact, that an unselected request returns
// the expected DECERR response, that downstream responses are muxed back
// upstream, and that request, response, and abort paths make forward progress
// through the per-downstream retiming.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_csr_demux_select_onehot_fpv_monitor #(
    parameter int AddrWidth = 1,
    parameter int DataWidth = 32,
    parameter int NumDownstreams = 1,
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic [NumDownstreams-1:0] select_onehot,

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
  logic decerr_resp_valid_next;
  logic decerr_resp_valid;
  logic fv_downstream_resp_valid;
  logic [NumDownstreams:0] downstream_resp_vec;
  logic [DownstreamWidth:0] downstream_resp_id;
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

  assign magic_upstream_req_valid = upstream_req_valid && select_onehot[d];
  assign abort_cntr_next = abort_cntr + upstream_req_abort - downstream_req_abort[d];
  assign decerr_resp_valid_next = upstream_req_valid && !(|select_onehot);

  // Count aborts through an arbitrary downstream retime path.
  `BR_REG(abort_cntr, abort_cntr_next)

  // An unselected request produces the internal DECERR response on the next cycle.
  `BR_REG(decerr_resp_valid, decerr_resp_valid_next)

  assign downstream_resp_vec = {decerr_resp_valid, downstream_resp_valid};
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

  // Valid requests either select exactly one downstream or request an internal DECERR.
  `BR_ASSUME(select_onehot0_a, upstream_req_valid |-> $onehot0(select_onehot))

  // The upstream agent issues at most one request until a response returns.
  `BR_ASSUME(only_one_outstanding_req_upstream_a, upstream_req_pending |-> !upstream_req_valid)

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_resp
    // Downstreams only respond to a request that is outstanding on that port.
    `BR_ASSUME(no_spurious_downstream_resp_a,
               downstream_resp_valid[i] |-> downstream_req_pending[i])
  end

  // ----------FV assertions----------
  // Requests selected for the arbitrary downstream preserve payload.
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
        upstream_req_addr,
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
  `BR_ASSERT(resp_upstream_onehot_a, $onehot0(downstream_resp_vec))

  // The demux does not issue a second request to a downstream with one still outstanding.
  `BR_ASSERT(only_one_outstanding_req_downstream_a,
             downstream_req_pending[d] |-> !downstream_req_valid[d])

  // Every upstream abort eventually reaches the selected downstream retime path.
  `BR_ASSERT(no_deadlock_abort_a, upstream_req_abort |-> s_eventually downstream_req_abort[d])

  // Every request selected for the arbitrary downstream eventually reaches that port.
  `BR_ASSERT(no_deadlock_downstream_req_a,
             magic_upstream_req_valid |-> s_eventually downstream_req_valid[d])

  // Every downstream or internal DECERR response eventually reaches the upstream interface.
  `BR_ASSERT(no_deadlock_upstream_resp_a,
             fv_downstream_resp_valid |-> s_eventually upstream_resp_valid)

endmodule : br_csr_demux_select_onehot_fpv_monitor

bind br_csr_demux_select_onehot br_csr_demux_select_onehot_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .NumDownstreams(NumDownstreams),
    .NumRetimeStages(NumRetimeStages)
) monitor (.*);
