// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Fixed-Priority APB Mux
//
// Routes one of several upstream APB interfaces to a shared downstream
// interface. In Setup, the lowest-index pending upstream is selected
// combinationally to drive the downstream setup phase. The winner is saved at
// the setup-to-access transition and held until the downstream access completes.
// This adds no arbitration cycle, but puts priority selection on the downstream
// request timing path. Only the access state and the winner are stored.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_apb_mux #(
    parameter int AddrWidth = 12,  // Must be at least 1
    parameter int NumUpstreams = 1  // Must be at least 1
) (
    input logic clk,
    input logic rst,

    input logic [NumUpstreams-1:0][AddrWidth-1:0] upstream_paddr,
    input logic [NumUpstreams-1:0] upstream_psel,
    input logic [NumUpstreams-1:0] upstream_penable,
    input logic [NumUpstreams-1:0][br_amba::ApbProtWidth-1:0] upstream_pprot,
    input logic [NumUpstreams-1:0][3:0] upstream_pstrb,
    input logic [NumUpstreams-1:0] upstream_pwrite,
    input logic [NumUpstreams-1:0][31:0] upstream_pwdata,
    output logic [NumUpstreams-1:0][31:0] upstream_prdata,
    output logic [NumUpstreams-1:0] upstream_pready,
    output logic [NumUpstreams-1:0] upstream_pslverr,

    output logic [AddrWidth-1:0] downstream_paddr,
    output logic downstream_psel,
    output logic downstream_penable,
    output logic [br_amba::ApbProtWidth-1:0] downstream_pprot,
    output logic [3:0] downstream_pstrb,
    output logic downstream_pwrite,
    output logic [31:0] downstream_pwdata,
    input logic [31:0] downstream_prdata,
    input logic downstream_pready,
    input logic downstream_pslverr
);
  // Integration Checks

  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_num_upstreams_a, NumUpstreams >= 1)

  for (genvar i = 0; i < NumUpstreams; i++) begin : gen_upstream_checks
    `BR_ASSERT_INTG(enable_requires_select_a, upstream_penable[i] |-> upstream_psel[i])
    `BR_ASSERT_INTG(access_stable_while_waiting_a,
                    (upstream_psel[i] && upstream_penable[i] && !upstream_pready[i]) |=>
                    upstream_psel[i] && upstream_penable[i])
    `BR_ASSERT_INTG(request_stable_while_pending_a,
                    (upstream_psel[i] && (!upstream_penable[i] || !upstream_pready[i])) |=>
                    upstream_psel[i] && $stable(
                        upstream_paddr[i]
                    ) && $stable(
                        upstream_pprot[i]
                    ) && $stable(
                        upstream_pstrb[i]
                    ) && $stable(
                        upstream_pwrite[i]
                    ) && $stable(
                        upstream_pwdata[i]
                    ))
  end

  // Implementation

  typedef enum logic {
    Setup  = 1'b0,
    Access = 1'b1
  } apb_state_t;

  typedef struct packed {
    logic [AddrWidth-1:0] addr;
    logic [br_amba::ApbProtWidth-1:0] prot;
    logic [3:0] strb;
    logic write;
    logic [31:0] wdata;
  } req_t;

  // Two states intentionally use a single flop.
  apb_state_t apb_state;  // ri lint_check_waive ONE_BIT_STATE_REG
  apb_state_t apb_state_next;
  logic any_grant;
  logic grant_winner_load;
  logic [NumUpstreams-1:0] grant;
  logic [NumUpstreams-1:0] grant_winner;
  logic [NumUpstreams-1:0] request_select;
  req_t [NumUpstreams-1:0] upstream_req;
  req_t downstream_req;

  br_arb_fixed #(
      .NumRequesters(NumUpstreams)
  ) br_arb_fixed (
      .clk,
      .rst,
      .request(upstream_psel),
      .grant
  );

  assign any_grant = |upstream_psel;

  `BR_REGI(apb_state, apb_state_next, Setup)
  `BR_REGL(grant_winner, grant, grant_winner_load)

  always_comb begin
    apb_state_next = apb_state;
    grant_winner_load = 1'b0;
    request_select = '0;
    downstream_psel = 1'b0;
    downstream_penable = 1'b0;
    upstream_pready = '0;
    upstream_pslverr = '0;

    unique case (apb_state)
      Setup: begin
        // An asserted request turns this cycle into downstream setup.
        request_select  = grant;
        downstream_psel = any_grant;
        if (any_grant) begin
          apb_state_next = Access;
          grant_winner_load = 1'b1;
        end
      end
      Access: begin
        request_select = grant_winner;
        downstream_psel = 1'b1;
        downstream_penable = 1'b1;
        upstream_pready = grant_winner & upstream_penable & {NumUpstreams{downstream_pready}};
        upstream_pslverr = grant_winner & upstream_penable & {NumUpstreams{downstream_pslverr}};

        if (downstream_pready) begin
          apb_state_next = Setup;
        end
      end
      default: begin
        // Both binary encodings are covered; recover from unknowns in simulation.
        apb_state_next = Setup;  // ri lint_check_waive UNREACHABLE
      end
    endcase
  end

  for (genvar i = 0; i < NumUpstreams; i++) begin : gen_upstream
    assign upstream_req[i] = '{
            addr: upstream_paddr[i],
            prot: upstream_pprot[i],
            strb: upstream_pstrb[i],
            write: upstream_pwrite[i],
            wdata: upstream_pwdata[i]
        };
  end

  br_mux_onehot #(
      .NumSymbolsIn(NumUpstreams),
      .SymbolWidth ($bits(req_t))
  ) br_mux_onehot_req (
      .select(request_select),
      .in(upstream_req),
      .out(downstream_req)
  );

  assign upstream_prdata   = {NumUpstreams{downstream_prdata}};
  assign downstream_paddr  = downstream_req.addr;
  assign downstream_pprot  = downstream_req.prot;
  assign downstream_pstrb  = downstream_req.strb;
  assign downstream_pwrite = downstream_req.write;
  assign downstream_pwdata = downstream_req.wdata;

  // Implementation Checks

  `BR_ASSERT_IMPL(grant_winner_onehot0_a, $onehot0(grant_winner))
  `BR_ASSERT_IMPL(active_grant_onehot_a, downstream_psel |-> $onehot(request_select))
  `BR_ASSERT_IMPL(downstream_enable_requires_select_a, downstream_penable |-> downstream_psel)
  `BR_ASSERT_IMPL(setup_advances_to_access_a,
                  (downstream_psel && !downstream_penable) |=> downstream_penable)
  `BR_ASSERT_IMPL(grant_stable_while_active_a, (apb_state == Access) |=> $stable(grant_winner))
  `BR_ASSERT_IMPL(
      downstream_completion_returns_setup_a,
      (downstream_psel && downstream_penable && downstream_pready) |=> apb_state == Setup)

endmodule : br_apb_mux
