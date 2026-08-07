// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL APB Demux with Onehot Select
//
// Routes an APB transfer according to a onehot selection input. Responses from
// downstream interfaces are muxed together and passed upstream. Each downstream
// interface can independently insert APB timing slices.
//
// When enabled, a selected transfer with no matching downstream completes with
// PSLVERR.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_apb_demux_select_onehot #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int NumDownstreams = 1,  // Must be at least 1
    parameter bit EnableDecodeError = 1,
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0}
) (
    input logic clk,
    input logic rst,

    // For an active transfer, select one downstream or leave all zero.
    input logic [NumDownstreams-1:0] select_onehot,

    input logic [AddrWidth-1:0] upstream_paddr,
    input logic upstream_psel,
    input logic upstream_penable,
    input logic [br_amba::ApbProtWidth-1:0] upstream_pprot,
    input logic [3:0] upstream_pstrb,
    input logic upstream_pwrite,
    input logic [31:0] upstream_pwdata,
    output logic [31:0] upstream_prdata,
    output logic upstream_pready,
    output logic upstream_pslverr,

    output logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_paddr,
    output logic [NumDownstreams-1:0] downstream_psel,
    output logic [NumDownstreams-1:0] downstream_penable,
    output logic [NumDownstreams-1:0][br_amba::ApbProtWidth-1:0] downstream_pprot,
    output logic [NumDownstreams-1:0][3:0] downstream_pstrb,
    output logic [NumDownstreams-1:0] downstream_pwrite,
    output logic [NumDownstreams-1:0][31:0] downstream_pwdata,
    input logic [NumDownstreams-1:0][31:0] downstream_prdata,
    input logic [NumDownstreams-1:0] downstream_pready,
    input logic [NumDownstreams-1:0] downstream_pslverr
);
  // Integration Checks

  logic upstream_access_waiting;
  logic upstream_request_pending;

  assign upstream_access_waiting  = upstream_psel && upstream_penable && !upstream_pready;
  assign upstream_request_pending = upstream_psel && (!upstream_penable || !upstream_pready);

  `BR_ASSERT_STATIC(legal_num_downstreams_a, NumDownstreams >= 1)
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 12)
  `BR_ASSERT_INTG(enable_requires_select_a, upstream_penable |-> upstream_psel)
  `BR_ASSERT_INTG(access_stable_while_waiting_a,
                  upstream_access_waiting |=> upstream_psel && upstream_penable)
  `BR_ASSERT_INTG(
      request_stable_while_pending_a,
      upstream_request_pending |=> upstream_psel && $stable(select_onehot) && $stable
      ({upstream_paddr, upstream_pprot, upstream_pstrb, upstream_pwrite, upstream_pwdata}))
  `BR_UNUSED(upstream_access_waiting)
  `BR_UNUSED(upstream_request_pending)

  // Implementation

  typedef struct packed {
    logic [31:0] rdata;
    logic ready;
    logic slverr;
  } resp_t;

  logic [NumDownstreams-1:0] downstream_req_valid_int;
  logic [NumDownstreams-1:0][31:0] downstream_prdata_int;
  logic [NumDownstreams-1:0] downstream_pready_int;
  logic [NumDownstreams-1:0] downstream_pslverr_int;
  resp_t [NumDownstreams-1:0] downstream_resp;
  resp_t upstream_resp;

  assign downstream_req_valid_int = select_onehot & {NumDownstreams{upstream_psel}};

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream
    `BR_ASSERT_STATIC(legal_num_retime_stages_a, NumRetimeStages[i] >= 0)

    if (NumRetimeStages[i] == 0) begin : gen_no_retime
      `BR_UNUSED(clk)
      `BR_UNUSED(rst)

      assign downstream_paddr[i] = upstream_paddr;
      assign downstream_psel[i] = downstream_req_valid_int[i];
      assign downstream_penable[i] = downstream_req_valid_int[i] && upstream_penable;
      assign downstream_pprot[i] = upstream_pprot;
      assign downstream_pstrb[i] = upstream_pstrb;
      assign downstream_pwrite[i] = upstream_pwrite;
      assign downstream_pwdata[i] = upstream_pwdata;
      assign downstream_prdata_int[i] = downstream_prdata[i];
      assign downstream_pready_int[i] = downstream_pready[i];
      assign downstream_pslverr_int[i] = downstream_pslverr[i];
    end else begin : gen_retime
      logic [NumRetimeStages[i]:0][AddrWidth-1:0] paddr;
      logic [NumRetimeStages[i]:0] psel;
      logic [NumRetimeStages[i]:0] penable;
      logic [NumRetimeStages[i]:0][br_amba::ApbProtWidth-1:0] pprot;
      logic [NumRetimeStages[i]:0][3:0] pstrb;
      logic [NumRetimeStages[i]:0] pwrite;
      logic [NumRetimeStages[i]:0][31:0] pwdata;
      logic [NumRetimeStages[i]:0][31:0] prdata;
      logic [NumRetimeStages[i]:0] pready;
      logic [NumRetimeStages[i]:0] pslverr;

      assign paddr[0] = upstream_paddr;
      assign psel[0] = downstream_req_valid_int[i];
      assign penable[0] = downstream_req_valid_int[i] && upstream_penable;
      assign pprot[0] = upstream_pprot;
      assign pstrb[0] = upstream_pstrb;
      assign pwrite[0] = upstream_pwrite;
      assign pwdata[0] = upstream_pwdata;
      assign prdata[NumRetimeStages[i]] = downstream_prdata[i];
      assign pready[NumRetimeStages[i]] = downstream_pready[i];
      assign pslverr[NumRetimeStages[i]] = downstream_pslverr[i];

      for (genvar j = 0; j < NumRetimeStages[i]; j++) begin : gen_retime_stage
        br_amba_apb_timing_slice #(
            .AddrWidth(AddrWidth)
        ) br_amba_apb_timing_slice (
            .clk,
            .rst,
            .paddr_in(paddr[j]),
            .psel_in(psel[j]),
            .penable_in(penable[j]),
            .pprot_in(pprot[j]),
            .pstrb_in(pstrb[j]),
            .pwrite_in(pwrite[j]),
            .pwdata_in(pwdata[j]),
            .prdata_out(prdata[j]),
            .pready_out(pready[j]),
            .pslverr_out(pslverr[j]),
            .paddr_out(paddr[j+1]),
            .psel_out(psel[j+1]),
            .penable_out(penable[j+1]),
            .pprot_out(pprot[j+1]),
            .pstrb_out(pstrb[j+1]),
            .pwrite_out(pwrite[j+1]),
            .pwdata_out(pwdata[j+1]),
            .prdata_in(prdata[j+1]),
            .pready_in(pready[j+1]),
            .pslverr_in(pslverr[j+1])
        );
      end

      assign downstream_paddr[i] = paddr[NumRetimeStages[i]];
      assign downstream_psel[i] = psel[NumRetimeStages[i]];
      assign downstream_penable[i] = penable[NumRetimeStages[i]];
      assign downstream_pprot[i] = pprot[NumRetimeStages[i]];
      assign downstream_pstrb[i] = pstrb[NumRetimeStages[i]];
      assign downstream_pwrite[i] = pwrite[NumRetimeStages[i]];
      assign downstream_pwdata[i] = pwdata[NumRetimeStages[i]];
      assign downstream_prdata_int[i] = prdata[0];
      assign downstream_pready_int[i] = pready[0];
      assign downstream_pslverr_int[i] = pslverr[0];
    end

    assign downstream_resp[i] = '{
            rdata: downstream_prdata_int[i],
            ready: downstream_pready_int[i],
            slverr: downstream_pslverr_int[i]
        };
  end

  if (EnableDecodeError) begin : gen_decode_error
    resp_t decode_error_resp;
    logic  decode_miss;

    assign decode_miss = upstream_psel && !(|select_onehot);
    assign decode_error_resp = '{rdata: '0, ready: 1'b1, slverr: 1'b1};

    br_mux_onehot #(
        .NumSymbolsIn(NumDownstreams + 1),
        .SymbolWidth ($bits(resp_t))
    ) br_mux_onehot_resp (
        .select({decode_miss, downstream_req_valid_int}),
        .in({decode_error_resp, downstream_resp}),
        .out(upstream_resp)
    );
  end else begin : gen_no_decode_error
    br_mux_onehot #(
        .NumSymbolsIn(NumDownstreams),
        .SymbolWidth ($bits(resp_t))
    ) br_mux_onehot_resp (
        .select(downstream_req_valid_int),
        .in(downstream_resp),
        .out(upstream_resp)
    );
  end

  assign upstream_prdata  = upstream_resp.rdata;
  assign upstream_pready  = upstream_psel && upstream_penable && upstream_resp.ready;
  assign upstream_pslverr = upstream_psel && upstream_penable && upstream_resp.slverr;

endmodule : br_apb_demux_select_onehot
