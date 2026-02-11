// SPDX-License-Identifier: Apache-2.0

// A buffer for requests to a flow-controlled interface that handles the
// SCB abort mechanism.
// If a request is backpressured, the buffer will hold the request until it is
// either accepted or the requester aborts the request.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_csr_request_reg #(
    parameter int RequestWidth = 1,
    parameter bit RegisterPopOutputs = 0
) (
    input logic clk,
    input logic rst,

    input logic push_valid,
    input logic push_abort,
    input logic [RequestWidth-1:0] push_req,

    input logic pop_ready,
    output logic pop_valid,
    output logic [RequestWidth-1:0] pop_req
);

  if (RegisterPopOutputs) begin : gen_reg_outputs
    logic pop_valid_next;

    // The logic here is similar to br_flow_reg_fwd, except we need to drop the
    // buffered request if push_abort is asserted.
    assign pop_valid_next = (push_valid || (pop_valid && !pop_ready)) && !push_abort;

    `BR_REG(pop_valid, pop_valid_next)
    `BR_REGL(pop_req, push_req, push_valid)

    `BR_ASSERT_IMPL(no_request_buffered_when_pushed_a, push_valid |-> !pop_valid)
  end else begin : gen_no_reg_outputs
    // Even if the output interface isn't registered, we still need to buffer
    // the request if it is backpressured.
    // The logic here is similar to br_flow_reg_rev/br_flow_reg_none, except we clear
    // the buf request if push_abort is asserted.
    logic buf_valid, buf_valid_next;
    logic [RequestWidth-1:0] buf_req;

    // Set buf_valid if there is a push_valid but the request is backpressured
    // Clear if the buf request is accepted or the request is aborted
    assign buf_valid_next = pop_valid && !pop_ready && !push_abort;
    assign pop_valid = push_valid || buf_valid;
    assign pop_req = buf_valid ? buf_req : push_req;

    `BR_REG(buf_valid, buf_valid_next)
    `BR_REGL(buf_req, push_req, push_valid && !pop_ready)

    `BR_ASSERT_IMPL(no_request_buffered_when_pushed_a, push_valid |-> !buf_valid)
  end

  // Implementation checks
  `BR_ASSERT_IMPL(pop_valid_stable_without_abort_a,
                  (pop_valid && !pop_ready && !push_abort) |=> pop_valid)
  `BR_ASSERT_IMPL(pop_req_stable_without_abort_a,
                  (pop_valid && !pop_ready && !push_abort) |=> pop_req == $past(pop_req))
  `BR_ASSERT_IMPL(pop_cleared_on_abort_a, push_abort |=> !pop_valid)

endmodule
