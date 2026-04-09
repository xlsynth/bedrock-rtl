// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"

module fv_valid_ready_check #(
    parameter bit Master = 1,
    parameter int PayloadWidth = 1,
    // Assertion options only used when Master=0
    parameter bit EnableAssertValidStability = 1,
    parameter bit EnableAssertPayloadStability = 1
) (
    input logic                    clk,
    input logic                    rst,
    input logic                    ready,
    input logic                    valid,
    input logic [PayloadWidth-1:0] payload
);

  `BR_ASSERT_STATIC(payload_width_gte_1_a, PayloadWidth >= 1)

  if (Master) begin : gen_master
    `BR_ASSUME(valid_stable_until_ready_a, valid && !ready |=> valid)
    `BR_ASSUME(payload_stable_until_ready_a, valid && !ready |=> $stable(payload))
  end else begin : gen_slave
    if (EnableAssertValidStability) begin : gen_assert_valid_stable
      `BR_ASSERT(valid_stable_until_ready_a, valid && !ready |=> valid)
    end else begin : gen_cover_valid_unstable
      `BR_COVER(valid_unstable_a, valid && !ready ##1 !valid)
    end
    if (EnableAssertPayloadStability) begin : gen_assert_payload_stable
      `BR_ASSERT(payload_stable_until_ready_a, valid && !ready |=> $stable(payload))
    end else begin : gen_cover_payload_unstable
      `BR_COVER(payload_unstable_a, valid && !ready ##1 !$stable(payload))
    end
  end

endmodule : fv_valid_ready_check
