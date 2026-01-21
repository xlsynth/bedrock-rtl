// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL SCB Demux FPV Monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_csr_demux_fpv_monitor #(
    parameter int AddrWidth = 1,
    parameter int DataWidth = 32,
    parameter int NumDownstreams = 1,
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
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

    // Inclusive min and max addresses for each downstream interface
    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_limit,

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
  logic [NumDownstreams-1:0] downstream_req_pending;
  logic [DownstreamWidth-1:0] d;
  logic magic_upstream_req_valid;
  logic [31:0] abort_cntr;
  logic upstream_addr_hit;
  logic upstream_decerr_valid;
  logic fv_downstream_resp_valid;
  logic [NumDownstreams:0] downstream_resp_vec;
  logic [DownstreamWidth:0] downstream_resp_id;
  logic [DataWidth-1:0] fv_downstream_resp_rdata;
  logic fv_downstream_resp_decerr;
  logic fv_downstream_resp_slverr;

  always_ff @(posedge clk) begin
    if (rst || upstream_resp_valid) begin
      upstream_req_pending <= 1'b0;
    end else if (upstream_req_valid) begin
      upstream_req_pending <= 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      downstream_req_pending <= '0;
    end else begin
      for (int i = 0; i < NumDownstreams; i++) begin
        if (downstream_req_valid[i]) begin
          downstream_req_pending[i] <= 1'b1;
        end else if (downstream_resp_valid[i]) begin
          downstream_req_pending[i] <= 1'b0;
        end
      end
    end
  end

  assign magic_upstream_req_valid = upstream_req_valid &&
                                   (upstream_req_addr >= downstream_addr_base[d]) &&
                                   (upstream_req_addr <= downstream_addr_limit[d]);
  // abort is broadcasted to all downstreams
  // If there is no active request on a branch, the abort signal will be ignored.
  `BR_REG(abort_cntr, abort_cntr + upstream_req_abort - downstream_req_abort[d])
  // If we get a request that doesn't match any downstream address range,
  // send a response with decerr=1.
  always_comb begin
    upstream_addr_hit = 1'b0;
    for (int i = 0; i < NumDownstreams; i++) begin
      if ((upstream_req_addr >= downstream_addr_base[i]) &&
          (upstream_req_addr <= downstream_addr_limit[i])) begin
        upstream_addr_hit = 1'b1;
        break;
      end
    end
  end
  assign upstream_decerr_valid = upstream_req_valid && !upstream_addr_hit;

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
  // If we get a request that doesn't match any downstream address range,
  // send back {rdata: '0, decerr: 1'b1, slverr: 1'b0}
  assign fv_downstream_resp_rdata = downstream_resp_id == NumDownstreams ?
                                    DataWidth'(0) : downstream_resp_rdata[downstream_resp_id];
  assign fv_downstream_resp_decerr = downstream_resp_id == NumDownstreams ?
                                     1'b1 : downstream_resp_decerr[downstream_resp_id];
  assign fv_downstream_resp_slverr = downstream_resp_id == NumDownstreams ?
                                     1'b0 : downstream_resp_slverr[downstream_resp_id];

  // ----------FV assumptions----------
  // pick a random downstream interface for assertions
  `BR_ASSUME(constant_d_a, $stable(d) && d < DownstreamWidth)
  `BR_ASSUME(only_one_outstanding_req_upstream_a, upstream_req_pending |-> !upstream_req_valid)
  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_addr
    `BR_ASSUME(legal_addr_range_a, downstream_addr_base[i] <= downstream_addr_limit[i])
    `BR_ASSUME(static_addr_a, $stable(downstream_addr_base[i]) && $stable(downstream_addr_limit[i]))
    `BR_ASSUME(no_spurious_downstream_resp_a,
               downstream_resp_valid[i] |-> downstream_req_pending[i])
  end

  for (genvar i = 0; i < NumDownstreams - 1; i++) begin : gen_i
    for (genvar j = i + 1; j < NumDownstreams; j++) begin : gen_j
      `BR_ASSUME(no_overlapping_addr_a,
                 downstream_addr_limit[i] < downstream_addr_base[j] ||
                downstream_addr_base[i] > downstream_addr_limit[j])
    end
  end

  // ----------FV assertions----------
  // upstream to downstream checks
  // upstream_req_abort is not a payload, it's a 1-cycle control signal
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

  // downstream to upstream checks
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

  // Pick a random downstream interface to check whether all upstream aborts are correctly propagated
  `BR_ASSERT(no_spurious_abort_a,
             (abort_cntr == 'd0) && !upstream_req_abort |-> !downstream_req_abort[d])
  `BR_ASSERT(resp_upstream_decerr_onehot_a, $onehot0(downstream_resp_vec))
  `BR_ASSERT(only_one_outstanding_req_downstream_a,
             downstream_req_pending[d] |-> !downstream_req_valid[d])
  `BR_ASSERT(no_deadlock_abort_a, upstream_req_abort |-> s_eventually downstream_req_abort[d])
  `BR_ASSERT(no_deadlock_downstream_req_a,
             magic_upstream_req_valid |-> s_eventually downstream_req_valid[d])
  `BR_ASSERT(no_deadlock_upstream_resp_a,
             fv_downstream_resp_valid |-> s_eventually upstream_resp_valid)

endmodule : br_csr_demux_fpv_monitor

bind br_csr_demux br_csr_demux_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .NumDownstreams(NumDownstreams),
    .NumRetimeStages(NumRetimeStages)
) monitor (.*);
