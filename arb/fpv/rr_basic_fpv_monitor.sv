// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Round Robin Arbiter basic FV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module rr_basic_fpv_monitor #(
    // Must be at least 1
    parameter int NumRequesters = 1,
    parameter bit EnableAssertPushValidStability = 1
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

  // ----------FV Modeling Code----------
  logic [$clog2(NumRequesters)-1:0] i, j;
  if (NumRequesters > 1) begin : gen_ij
    `BR_FV_2RAND_IDX(i, j, NumRequesters)
  end else begin : gen_i
    assign i = 0;
  end
  logic [NumRequesters-1:0] high_priority_request;

  `BR_REGL(high_priority_request, (grant == 1 << (NumRequesters - 1)) ? 'd1 : grant << 1,
           (grant != 0) && enable_priority_update)

  // ----------Sanity Check----------
  // High priority request must be grant the same cycle
  `BR_ASSERT(high_priority_grant_a, request[i] && high_priority_request[i] |-> grant[i])

  // ----------Fairness Check----------
  if (NumRequesters > 1) begin : gen_multi_req
    `BR_ASSERT(arb_priority_a,
               grant[j] |-> !request[i] ||  // high_priority ... j ... i
               ((2 ** j >= high_priority_request) && (2 ** i > high_priority_request) && (j < i)) ||
               // i ... high_priority ... j
               ((2 ** j >= high_priority_request) && (2 ** i < high_priority_request)) ||
               // j ... i ... high_priority ...
               ((2 ** j <= high_priority_request) && (2 ** i < high_priority_request) && (j < i)))

    if (EnableAssertPushValidStability) begin : gen_req_stable
      `BR_ASSERT(
          round_robin_a,
          request[i] |-> not (!grant[i] && enable_priority_update throughout grant[j] [-> 2]))
    end
  end

  // ----------Critical Covers----------
  generate
    for (genvar i = 0; i < NumRequesters; i++) begin : gen_cov
      // Make sure every port can reach highest priority
      `BR_COVER(priority_c, high_priority_request[i])
      `BR_COVER(low_priority_grant_c, request[i] && !high_priority_request[i] && grant[i])
    end
  endgenerate

endmodule : rr_basic_fpv_monitor
