`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_amba_iso_req_tracker #(
    parameter  int MaxOutstanding   = 128,
    // Can be set to 1 for AXI-Lite or write responses, otherwise should
    // be set to br_amba::AxiBurstLenWidth.
    parameter  int MaxAxiBurstLen   = 2 ** br_amba::AxiBurstLenWidth,
    localparam int AxiBurstLenWidth = br_math::clamped_clog2(MaxAxiBurstLen)
) (
    input logic clk,
    input logic rst,
    // AW or AR channel from upstream
    output logic upstream_axready,
    input logic upstream_axvalid,
    input logic [AxiBurstLenWidth-1:0] upstream_axlen,
    // R or B channel to upstream
    input logic upstream_xready,
    output logic upstream_xvalid,
    // AW or AR channel to downstream
    input logic downstream_axready,
    output logic downstream_axvalid,
    output logic [AxiBurstLenWidth-1:0] downstream_axlen,
    // R or B channel to downstream
    output logic downstream_xready,
    input logic downstream_xvalid,
    // Isolate request
    input logic isolate_req,
    output logic isolate_done
);

  // Integration checks
  `BR_ASSERT_STATIC(max_outstanding_gte_1_a, MaxOutstanding > 1)
  `BR_ASSERT_STATIC(max_axi_burst_len_1_or_amba_a,
                    MaxAxiBurstLen == 1 || MaxAxiBurstLen == 2 ** br_amba::AxiBurstLenWidth)
  // Check that the isolate request can only rise when isolate_done is false.
  `BR_ASSERT_INTG(legal_request_rise_a, $rose(isolate_req) |-> !isolate_done)
  // Check that the isolate request can only fall when isolate_done is true.
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(isolate_req) |-> isolate_done)

  // Local parameters
  localparam bit SingleBeatOnly = (MaxAxiBurstLen == 1);
  localparam int MaxBeats = MaxAxiBurstLen * MaxOutstanding;
  localparam int MaxBeatCountWidth = $clog2(MaxBeats + 1);
  localparam int IncrWidth = $clog2(MaxAxiBurstLen + 1);

  // Local signals
  logic [IncrWidth-1:0] incr_count;
  logic incr_valid;
  logic decr_valid;
  logic [MaxBeatCountWidth-1:0] expected_resp_count;
  logic isolated;

  //
  // Implementation
  //

  // Counter

  // Increment counter by number of expected responses whenever a request is accepted on
  // the downstream side.
  assign incr_valid = downstream_axvalid && downstream_axready;
  if (SingleBeatOnly) begin : gen_single_beat_only
    assign incr_count = 1'b1;
    assign downstream_axlen = '0;
    `BR_UNUSED(upstream_axlen)
  end else begin : gen_multi_beat
    assign downstream_axlen = upstream_axlen;
    assign incr_count = downstream_axlen + 1'b1;
  end

  // Decrement counter by 1 whenever a response is returned from the downstream side.
  assign decr_valid = upstream_xvalid && upstream_xready;

  br_counter #(
      .MaxValue(MaxBeats),
      .MaxChange(MaxAxiBurstLen),
      .EnableWrap(0),
      .EnableSaturate(0)
  ) br_counter_exp_resp_count (
      .clk,
      .rst,
      //
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid,
      .incr(incr_count),
      .decr_valid,
      .decr(IncrWidth'(1'b1)),
      .value(expected_resp_count),
      .value_next()
  );

  // block upstream->downstream requests when it is isolated
  assign upstream_axready = downstream_axready && !isolated;
  assign downstream_axvalid = upstream_axvalid && !isolated;

  // accept, but don't forward new responses when isolated
  assign upstream_xvalid = downstream_xvalid && !isolated;
  assign downstream_xready = upstream_xready || isolated;

  // FSM
  logic isolate_done_next;
  `BR_REG(isolate_done, isolate_done_next)

  assign isolate_done_next = isolate_done ?
      // Deassert isolate_done only if isolate_req is dropped and expected_resp_count is 0.
      (expected_resp_count == '0 && !isolate_req)
      // Assert isolate_done if isolate_req is asserted (i.e. isolate_req is handled immediately)
      : isolate_req;

  // Start blocking traffic as soon as isolate_req is asserted, and continue until
  // isolate_done is deasserted.
  assign isolated = isolate_req || isolate_done;

endmodule
