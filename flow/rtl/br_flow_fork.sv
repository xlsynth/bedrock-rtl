// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL Flow Fork
//
// Forks a dataflow pipeline into a number of downstream pipelines.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards. This module does not implement
// the datapath.

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_flow_fork #(
    parameter int NumForks = 2  // Must be at least 2
)(
    input logic clk,  // Used only for assertions
    input logic rst,  // Used only for assertions

    // Push-side interface
    output logic push_ready,
    input  logic push_valid,

    // Forked pop-side interfaces
    //
    // pop_valid signals are unstable because they must fall if another pop_ready falls.
    // There is no dependency between pop_valid[i] and pop_ready[i].
    input  logic [NumForks-1:0] pop_ready,
    output logic [NumForks-1:0] pop_valid_unstable
);

    //------------------------------------------
    // Integration checks
    //------------------------------------------
    `BR_ASSERT_STATIC(NumForksMustBeAtLeastTwo_A, NumForks >= 2)
    `BR_ASSERT_INTG(push_backpressure_intg_A, !push_ready && push_valid |=> push_valid)

    //------------------------------------------
    // Implementation
    //------------------------------------------
    for (int i = 0; i < NumForks; i++) begin : gen_forks
        always_comb begin
            pop_valid[i] = push_valid;
            for (int j = 0; j < NumForks; j++) begin
                if (i != j) begin
                    pop_valid[i] &= pop_ready[j];
                end
            end
        end
    end
    
    //------------------------------------------
    // Implementation checks
    //------------------------------------------
    for (int i = 0; i < NumForks; i++) begin : gen_fork_checks
        `BR_COVER_IMPL(pop_valid_unstable_C, $stable(push_valid) && $fell(pop_valid[i]))
    end

endmodule : br_flow_fork
