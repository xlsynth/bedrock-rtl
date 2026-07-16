// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL APB Demux Select-Onehot FPV Monitor
//
// Testplan
//
// Design specification:
// - Route each active upstream APB transfer to the downstream selected by
//   select_onehot. At most one downstream may be selected for a transfer.
// - Preserve PADDR, PPROT, PSTRB, PWRITE, and PWDATA on the selected request.
// - Allow each downstream path to contain an independent number of APB timing
//   slices while preserving protocol behavior and transaction contents.
// - Return the selected downstream PRDATA, PREADY, and PSLVERR response upstream.
// - When EnableDecodeError is set, complete an active transfer with zero
//   PRDATA and asserted PSLVERR when no downstream is selected. Otherwise,
//   require every active transfer to select a downstream.
//
// Input assumptions:
// - The upstream interface follows the APB4 manager protocol, including stable
//   request control and payload while an access is waiting.
// - PWDATA also remains stable for pending reads because the RTL integration
//   contract treats the complete request bundle uniformly.
// - select_onehot is onehot-or-zero for an active transfer when decode errors
//   are enabled, and exactly onehot otherwise. It remains stable until that
//   transfer completes.
// - Every downstream response interface follows the APB4 subordinate protocol.
//
// Checks:
// - Apply APB4 protocol VIP to the upstream and every downstream interface.
// - Prove that only the selected downstream is activated and that request
//   control and payload arrive unchanged, including through retimed paths.
// - Prove that selected downstream responses return upstream unchanged.
// - When decode errors are enabled, prove that a decode miss activates no
//   downstream and completes upstream with zero PRDATA and PSLVERR.
// - Cover each destination, reads, writes, wait states, error responses, mixed
//   zero/nonzero retiming configurations, and decode misses when enabled.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_apb_demux_select_onehot_fpv_monitor #(
    parameter int AddrWidth = 12,
    parameter int NumDownstreams = 1,
    parameter bit EnableDecodeError = 1,
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0}
) (
    input logic clk,
    input logic rst,

    input logic [NumDownstreams-1:0] select_onehot,

    input logic [AddrWidth-1:0] upstream_paddr,
    input logic upstream_psel,
    input logic upstream_penable,
    input logic [br_amba::ApbProtWidth-1:0] upstream_pprot,
    input logic [3:0] upstream_pstrb,
    input logic upstream_pwrite,
    input logic [31:0] upstream_pwdata,
    input logic [31:0] upstream_prdata,
    input logic upstream_pready,
    input logic upstream_pslverr,

    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_paddr,
    input logic [NumDownstreams-1:0] downstream_psel,
    input logic [NumDownstreams-1:0] downstream_penable,
    input logic [NumDownstreams-1:0][br_amba::ApbProtWidth-1:0] downstream_pprot,
    input logic [NumDownstreams-1:0][3:0] downstream_pstrb,
    input logic [NumDownstreams-1:0] downstream_pwrite,
    input logic [NumDownstreams-1:0][31:0] downstream_pwdata,
    input logic [NumDownstreams-1:0][31:0] downstream_prdata,
    input logic [NumDownstreams-1:0] downstream_pready,
    input logic [NumDownstreams-1:0] downstream_pslverr
);

  typedef struct packed {
    logic [AddrWidth-1:0] paddr;
    logic [br_amba::ApbProtWidth-1:0] pprot;
    logic [3:0] pstrb;
    logic pwrite;
    logic [31:0] pwdata;
  } req_payload_t;

  typedef struct packed {
    logic [31:0] prdata;
    logic pslverr;
  } resp_payload_t;

  localparam int ReqPayloadWidth = $bits(req_payload_t);
  localparam int RespPayloadWidth = $bits(resp_payload_t);
  localparam int DownstreamWidth = NumDownstreams == 1 ? 1 : $clog2(NumDownstreams);

  logic [DownstreamWidth-1:0] magic_d;
  req_payload_t upstream_req_payload;
  req_payload_t downstream_req_payload;
  resp_payload_t downstream_resp_payload;
  resp_payload_t upstream_resp_payload;
  logic upstream_req_start;
  logic downstream_req_start;
  logic downstream_resp_complete;
  logic upstream_resp_complete;
  logic decode_miss;
  logic decode_miss_response_ok;

  assign upstream_req_payload = '{
          paddr: upstream_paddr,
          pprot: upstream_pprot,
          pstrb: upstream_pstrb,
          pwrite: upstream_pwrite,
          pwdata: upstream_pwdata
      };
  assign downstream_req_payload = '{
          paddr: downstream_paddr[magic_d],
          pprot: downstream_pprot[magic_d],
          pstrb: downstream_pstrb[magic_d],
          pwrite: downstream_pwrite[magic_d],
          pwdata: downstream_pwdata[magic_d]
      };
  assign downstream_resp_payload = '{
          prdata: downstream_prdata[magic_d],
          pslverr: downstream_pslverr[magic_d]
      };
  assign upstream_resp_payload = '{prdata: upstream_prdata, pslverr: upstream_pslverr};

  assign upstream_req_start = upstream_psel && !upstream_penable;
  assign decode_miss = upstream_psel && !(|select_onehot);
  assign decode_miss_response_ok = upstream_pready && upstream_pslverr && upstream_prdata == '0;
  assign downstream_req_start = downstream_psel[magic_d] && !downstream_penable[magic_d];
  assign downstream_resp_complete = downstream_psel[magic_d] && downstream_penable[magic_d] &&
                                    downstream_pready[magic_d];
  assign upstream_resp_complete = upstream_psel && upstream_penable && upstream_pready;

  // Pick one arbitrary downstream so a single checker proves every route.
  `BR_ASSUME(magic_d_constant_a, $stable(magic_d) && magic_d < NumDownstreams)

  if (EnableDecodeError) begin : gen_decode_error_contract
    // Decode-error mode permits zero select so the local error response can complete the transfer.
    `BR_ASSUME(select_onehot0_a, upstream_psel |-> $onehot0(select_onehot))
  end else begin : gen_no_decode_error_contract
    // Without a local decode-error response, every active transfer must select one downstream.
    `BR_ASSUME(select_onehot_a, upstream_psel |-> $onehot(select_onehot))
  end

  // Keep the route stable from the APB setup phase into the access phase.
  `BR_ASSUME(select_stable_after_setup_a, upstream_psel && !upstream_penable |=> $stable
                                          (select_onehot))

  // Keep the route stable while an APB access is stalled by the DUT response path.
  `BR_ASSUME(select_stable_while_waiting_a,
             upstream_psel && upstream_penable && !upstream_pready |=> $stable(select_onehot))

  // Cover the read-PWDATA stability gap left by APB VIP's write-only PWDATA checks.
  `BR_ASSUME(
      upstream_read_pwdata_stable_a,
      upstream_psel && (!upstream_penable || !upstream_pready) && !upstream_pwrite |=> $stable
      (upstream_pwdata))

  // Check legality and backpressure behavior of the upstream APB manager traffic.
  apb4_master #(
      .ABUS_WIDTH(AddrWidth)
  ) upstream (
      .pclk(clk),
      .presetn(!rst),
      .psel(upstream_psel),
      .penable(upstream_penable),
      .paddr(upstream_paddr),
      .pwrite(upstream_pwrite),
      .pwdata(upstream_pwdata),
      .pstrb(upstream_pstrb),
      .pprot(upstream_pprot),
      .pready(upstream_pready),
      .prdata(upstream_prdata),
      .pslverr(upstream_pslverr)
  );

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_vip
    // Check legality and backpressure behavior of each downstream APB subordinate.
    apb4_slave #(
        .ABUS_WIDTH(AddrWidth)
    ) downstream (
        .pclk(clk),
        .presetn(!rst),
        .psel(downstream_psel[i]),
        .penable(downstream_penable[i]),
        .paddr(downstream_paddr[i]),
        .pwrite(downstream_pwrite[i]),
        .pwdata(downstream_pwdata[i]),
        .pstrb(downstream_pstrb[i]),
        .pprot(downstream_pprot[i]),
        .pready(downstream_pready[i]),
        .prdata(downstream_prdata[i]),
        .pslverr(downstream_pslverr[i])
    );
  end

  // Preserve every request field and prevent missing or spurious downstream requests.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ReqPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(1)
  ) req_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(upstream_req_start && select_onehot[magic_d]),
      .incoming_data(upstream_req_payload),
      .outgoing_vld(downstream_req_start),
      .outgoing_data(downstream_req_payload)
  );

  // Return the selected downstream read data and error response upstream unchanged.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(RespPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(1)
  ) resp_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(downstream_resp_complete),
      .incoming_data(downstream_resp_payload),
      .outgoing_vld(upstream_resp_complete && select_onehot[magic_d]),
      .outgoing_data(upstream_resp_payload)
  );

  // No more than one downstream may be selected by the demux at a time.
  `BR_ASSERT(downstream_select_onehot0_a, $onehot0(downstream_psel))

  // Upstream completion and error outputs are only meaningful during an APB access phase.
  `BR_ASSERT(no_upstream_response_outside_access_a,
             (!upstream_psel || !upstream_penable) |-> !upstream_pready && !upstream_pslverr)

  if (EnableDecodeError) begin : gen_decode_error_checks
    // A decode miss must not activate any downstream interface.
    `BR_ASSERT(decode_miss_no_downstream_a, decode_miss |-> downstream_psel == '0)

    // A decode miss completes in the access phase with the specified error response.
    `BR_ASSERT(decode_miss_response_a, decode_miss && upstream_penable |-> decode_miss_response_ok)

    // Exercise the internal decode-miss completion path.
    `BR_COVER(decode_miss_c, decode_miss && upstream_penable && upstream_pready && upstream_pslverr)
  end

  // Every selected request eventually reaches its chosen finite retiming path.
  `BR_ASSERT(selected_request_progress_a,
             upstream_req_start && select_onehot[magic_d] |-> s_eventually downstream_req_start)

  // Every completed downstream response eventually returns through its finite retiming path.
  `BR_ASSERT(selected_response_progress_a,
             downstream_resp_complete |-> s_eventually upstream_resp_complete)

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_covers
    // Exercise a completed read transfer through this downstream.
    `BR_COVER(downstream_read_c,
              downstream_psel[i] && downstream_penable[i] && downstream_pready[i] &&
              !downstream_pwrite[i])

    // Exercise a completed write transfer through this downstream.
    `BR_COVER(
        downstream_write_c,
        downstream_psel[i] && downstream_penable[i] && downstream_pready[i] && downstream_pwrite[i])
  end

  // Exercise downstream backpressure propagating to the upstream access.
  `BR_COVER(wait_state_c, upstream_psel && upstream_penable && !upstream_pready)

  // Exercise a selected downstream error response returning upstream.
  `BR_COVER(selected_error_response_c,
            upstream_resp_complete && upstream_pslverr && (|select_onehot))

endmodule : br_apb_demux_select_onehot_fpv_monitor

bind br_apb_demux_select_onehot br_apb_demux_select_onehot_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .NumDownstreams(NumDownstreams),
    .EnableDecodeError(EnableDecodeError),
    .NumRetimeStages(NumRetimeStages)
) monitor (.*);
