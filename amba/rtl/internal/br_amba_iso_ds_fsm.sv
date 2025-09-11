// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_iso_ds_fsm (
    input  logic clk,
    input  logic rst,
    //
    input  logic isolate_req,
    output logic isolate_done,
    //
    output logic align_and_hold_req,
    input  logic align_and_hold_done,
    //
    output logic resp_tracker_isolate_req,
    input  logic resp_tracker_fifo_empty
);

  typedef enum logic [1:0] {
    Normal  = 2'b00,
    Isolate = 2'b01,
    Flush   = 2'b10
  } iso_ds_fsm_state_t;

  iso_ds_fsm_state_t state, state_next;
  `BR_REGI(state, state_next, Normal)

  `BR_ASSERT(fsm_state_legal_a, state == Normal || state == Isolate || state == Flush)
  always_comb begin
    case (state)
      Normal: begin
        state_next = isolate_req ? Isolate : state;
        //
        align_and_hold_req = 1'b0;
        resp_tracker_isolate_req = 1'b0;
        isolate_done = 1'b0;
      end
      Isolate: begin
        state_next = !isolate_req ? Flush : state;
        //
        align_and_hold_req = 1'b0;
        resp_tracker_isolate_req = 1'b1;
        isolate_done = 1'b1;
      end
      Flush: begin
        state_next = (align_and_hold_done && resp_tracker_fifo_empty) ? Normal : state;
        //
        align_and_hold_req = 1'b1;
        resp_tracker_isolate_req = 1'b1;
        isolate_done = 1'b1;
      end
      default: begin
        state_next = Normal;
        //
        align_and_hold_req = 1'b0;
        resp_tracker_isolate_req = 1'b0;
        isolate_done = 1'b0;
      end
    endcase
  end

endmodule
