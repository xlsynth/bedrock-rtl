// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AMBA AXI Upstream (Manager) Isolator State Machine
//
// This module is used to control the state of the AXI isolation
// upstream interface. It first blocks the upstream interface and forces
// alignment of the WDATA and AW channels. Once the alignment is complete,
// it continues to hold off the upstream interface until isolate_req is
// deasserted. Once isolate_req is deasserted, the module will wait for
// expected responses from the downstream interface to arrive and then
// will re-connect the upstream interface.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_iso_us_fsm (
    input  logic clk,
    input  logic rst,
    //
    input  logic isolate_req,
    output logic isolate_done,
    //
    output logic align_and_hold_req,
    input  logic align_and_hold_done,
    //
    output logic req_tracker_isolate_req,
    input  logic req_tracker_isolate_done
);

  typedef enum logic [1:0] {
    Normal = 2'b00,
    AlignWrite = 2'b01,
    Isolate = 2'b10,
    Flush = 2'b11
  } iso_us_fsm_state_t;

  iso_us_fsm_state_t state, state_next;
  `BR_REGI(state, state_next, Normal)

  `BR_ASSERT_KNOWN(fsm_state_known_a, state)
  always_comb begin
    unique case (state)
      Normal: begin
        state_next = isolate_req ? AlignWrite : state;
        //
        align_and_hold_req = 1'b0;
        req_tracker_isolate_req = 1'b0;
        isolate_done = 1'b0;
      end
      AlignWrite: begin
        state_next = align_and_hold_done ? Isolate : state;
        //
        align_and_hold_req = 1'b1;
        req_tracker_isolate_req = 1'b0;
        isolate_done = 1'b0;
      end
      Isolate: begin
        state_next = (!isolate_req && req_tracker_isolate_done) ? Flush : state;
        //
        align_and_hold_req = 1'b1;
        req_tracker_isolate_req = 1'b1;
        isolate_done = 1'b1;
      end
      Flush: begin
        state_next = !req_tracker_isolate_done ? Normal : state;
        //
        align_and_hold_req = 1'b1;
        req_tracker_isolate_req = 1'b0;
        isolate_done = 1'b1;
      end
      default: begin
        state_next = Normal;  // ri lint_check_waive UNREACHABLE
        //
        align_and_hold_req = 1'b0;
        req_tracker_isolate_req = 1'b0;
        isolate_done = 1'b0;
      end
    endcase
  end

endmodule
