// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Least-Recently-Used (LRU) Arbiter Core
//
// Combinationally selects the highest-priority active requester using an
// externally maintained pairwise priority matrix. priority_matrix[i][j] is
// high when requester i has higher priority than requester j. The diagonal
// is unused.

`include "br_asserts_internal.svh"

module br_arb_lru_core_internal #(
    // Must be at least 1
    parameter int NumRequesters = 1
) (
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][NumRequesters-1:0] priority_matrix,
    output logic [NumRequesters-1:0] can_grant,
    output logic [NumRequesters-1:0] grant
);

  `BR_ASSERT_STATIC(num_requesters_gte_1_A, NumRequesters >= 1)

  // A requester can only be granted if there are no higher-priority active requesters.
  always_comb begin
    can_grant = '1;
    for (int i = 0; i < NumRequesters; i++) begin
      for (int j = 0; j < NumRequesters; j++) begin
        if (i != j) begin
          can_grant[i] &= !request[j] || priority_matrix[i][j];
        end
      end
    end
  end

  assign grant = request & can_grant;

endmodule : br_arb_lru_core_internal
