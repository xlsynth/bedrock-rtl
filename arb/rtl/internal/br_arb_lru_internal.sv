// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Least-Recently-Used (LRU) Arbiter
//
// Grants a single request at a time with a fair least-recently-used policy.
//
// The enable_priority_update signal allows the priority state to update when a grant is made.
// If low, grants can still be made, but the priority will remain unchanged for the next cycle.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_arb_lru_internal #(
    // Must be at least 1
    parameter int NumRequesters = 1
) (
    // ri lint_check_waive INPUT_NOT_READ
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] can_grant,
    output logic [NumRequesters-1:0] grant
);

  `BR_ASSERT_STATIC(num_requesters_gte_1_A, NumRequesters >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  if (NumRequesters == 1) begin : gen_1_req
    `BR_UNUSED(rst)
    `BR_UNUSED(enable_priority_update)
    assign can_grant = 1'b1;
    assign grant = request;

  end else begin : gen_n_req

    // Whenever a requester is granted, it becomes the *most* recently used, and therefore
    // it becomes the lowest priority.
    //
    // To ensure fairness, we need to maintain a total order of least recently used requesters.
    // We do this with a priority state matrix, where state[i][j] == 1'b1 means that requester
    // i is less recently used than requester j (otherwise, i is more recently used than j and
    // has lower priority). This scheme is based on the matrix arbiter as described in Chapter
    // 18.5 of "Principles and Practices of Interconnection Networks" by Dally and Towles.
    //
    // Therefore, requester i can only be granted if (!req[j] || state[i][j]) for all j where i != j.
    // If priorities are tied, the lower-index requester wins.
    //
    // State update occurs whenever enable_priority_update is 1 and there is any valid request
    // (because it will always result in a grant).
    // * Whenever a grant occurs for requester i, on the next cycle we fill 0s into state[i][j]
    //   for all j where i != j. This indicates that requester i is used more recently (lower
    //   priority) than all requesters j.
    // * Whenever a grant occurs for requester j, on the next cycle we fill 1s into state[i][j]
    //   for all i where i != j. This indicates that all requesters i are used less recently
    //   (higher priority) than requester j.
    //
    // The advantage of this implementation is that we can update and search all the priorities
    // in parallel, which is good for timing. However, the priority state contains some redundancy,
    // costing extra flip-flops.


    logic [NumRequesters-1:0][NumRequesters-1:0] state;

    br_lru_state_internal #(
        .NumRequesters(NumRequesters)
    ) br_lru_state_internal (
        .clk,
        .rst,
        .update_priority(enable_priority_update && |request),
        .grant,
        .state
    );


    br_arb_pairwise_core_internal #(
        .NumRequesters(NumRequesters)
    ) br_arb_pairwise_core_internal (
        .request,
        .priority_matrix(state),
        .can_grant,
        .grant
    );
  end

endmodule : br_arb_lru_internal
