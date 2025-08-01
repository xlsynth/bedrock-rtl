// Copyright 2024-2025 The Bedrock-RTL Authors
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

// CDC synchronizer for a single bit level signal.

`include "br_registers.svh"
`include "br_asserts_internal.svh"
`include "br_gates.svh"
module br_cdc_bit_toggle #(
    // Number of synchronization stages. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumStages = 3,
    // If 1, add a flop on the source clock before the synchronizer
    parameter bit AddSourceFlop = 1
) (
    // Used for simulation delay modeling only
    // ri lint_check_waive INPUT_NOT_READ NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic src_clk,
    // Used for assertion only
    // ri lint_check_waive INPUT_NOT_READ NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic src_rst,
    input logic src_bit,

    // ri lint_check_waive ONE_LOCAL_CLOCK
    input  logic dst_clk,
    // Used for assertion only
    // ri lint_check_waive INPUT_NOT_READ NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic dst_rst,
    output logic dst_bit
);

  // Integration Assertions
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_one_a, NumStages >= 1)

  // TODO(zhemao): Add assertion to check that the source bit doesn't toggle too frequently
  // Main question: How frequent is too frequent?

  // Implementation
  logic src_bit_internal, src_bit_internal_maxdel;

  if (AddSourceFlop) begin : gen_src_flop
    `BR_REGNX(src_bit_internal, src_bit, src_clk)
  end else begin : gen_src_passthrough
    assign src_bit_internal = src_bit;
  end

`ifdef SIMULATION
  // The mux bit to select between src_bit_internal_maxdel and src_bit_delayed
  logic src_bit_delay_sel;
  logic src_bit_internal_delayed;
  logic src_bit_internal_final;

  // Delay the source bit by one source or destination clock
  always @(posedge src_clk or posedge dst_clk) begin
    src_bit_internal_delayed <= src_bit_internal;
  end

  assign src_bit_internal_final = src_bit_delay_sel ? src_bit_internal_delayed : src_bit_internal;

  // ri lint_check_off ONE_CONN_PER_LINE
  `BR_GATE_CDC_MAXDEL(src_bit_internal_maxdel, src_bit_internal_final)
  // ri lint_check_on ONE_CONN_PER_LINE

  initial begin
    string hier;
    int new_seed;
    #0;  // Wait for time 0 TB threads to complete
    if (br_cdc_pkg::cdc_delay_mode inside {br_cdc_pkg::CdcDelayRandOnce,
                                           br_cdc_pkg::CdcDelayRandAlways}) begin
      // Use the hierarchical name to generate a unique seed for each instantiation
      // This is to avoid all instantiations having the same random behavior.
      $sformat(hier, "%m");
      new_seed = $urandom;
      foreach (hier[i]) begin
        new_seed += (hier[i] << (i % 4));
      end
      process::self().srandom(new_seed);
    end
    case (br_cdc_pkg::cdc_delay_mode)
      br_cdc_pkg::CdcDelayNone:     src_bit_delay_sel = 1'b0;
      br_cdc_pkg::CdcDelayAlways:   src_bit_delay_sel = 1'b1;
      br_cdc_pkg::CdcDelayRandOnce: src_bit_delay_sel = $urandom_range(0, 1);
      br_cdc_pkg::CdcDelayRandAlways: begin
        bit do_randomize;
        src_bit_delay_sel = $urandom_range(0, 1);
        forever begin
          @(posedge dst_clk);
          if (src_bit_delay_sel != src_bit_internal_delayed) begin
            // For back to back source signal toggle, the signal could be dropped if the 1st
            // toggle chose the delayed version and the 2nd toggle chose the non-delayed version,
            // Avoid this situation here
            if (do_randomize || !src_bit_delay_sel) begin
              src_bit_delay_sel = $urandom_range(0, 1);
              do_randomize = 0;
            end
          end else begin
            do_randomize = 1;
          end
        end
      end
      default: begin
        $error("Invalid cdc_delay_mode %d", br_cdc_pkg::cdc_delay_mode);
        $finish;
      end
    endcase
  end

`else
  // ri lint_check_off ONE_CONN_PER_LINE
  `BR_GATE_CDC_MAXDEL(src_bit_internal_maxdel, src_bit_internal)
  // ri lint_check_on ONE_CONN_PER_LINE
`endif

  br_gate_cdc_sync #(
      .NumStages(NumStages)
  ) br_gate_cdc_sync (
      .clk(dst_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .in(src_bit_internal_maxdel),
      .out(dst_bit)
  );

endmodule
