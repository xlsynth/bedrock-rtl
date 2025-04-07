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

  typedef enum logic [2:0] {
    Normal,
    Isolate,
    Flush
  } iso_ds_fsm_state_t;

  iso_ds_fsm_state_t state, state_next;
  `BR_REG(state, state_next)

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
        `BR_ASSERT_IMM(invalid_state_a, 0)
        state_next = Normal;
        //
        align_and_hold_req = 1'b0;
        resp_tracker_isolate_req = 1'b0;
        isolate_done = 1'b0;
      end
    endcase
  end

endmodule
