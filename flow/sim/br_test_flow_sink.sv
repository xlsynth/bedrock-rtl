// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Test Flow Sink
//
// Testbench module that consumes a ready/valid data flow.
//
// After an optional startup delay, probabilistically asserts `push_ready` based on Rate,
// then holds `push_ready` high until a transfer occurs. Optionally checks received data
// against either an internal counter pattern or a provided `expected_data` array.
//
// Asserts `done` after NumValues transfers when data checking is enabled, and flags
// `error` on data mismatches or unexpected extra data

`include "br_registers.svh"

module br_test_flow_sink #(
    parameter int Width = 8,
    // If 1, count received data values and check against either a counter pattern
    // or the provided `expected_data` array.
    parameter bit CheckData = 1,
    parameter bit UseCounterPattern = 1,
    parameter int NumValues = 8,
    parameter real Rate = 1.0, // probability of asserting push_ready on an idle cycle [0.0 - 1.0]
    parameter int InitialDelay = 10, // cycles to wait before starting to accept data
    parameter int Seed = 1
) (
    input  logic             clk,
    input  logic             rst,

    // Used if CheckData is 1 and UseCounterPattern is 0, otherwise ignored
    input  logic [NumValues-1:0][Width-1:0] expected_data,
    
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    output logic             done,  // Asserted once NumValues received and CheckData is 1
    output logic             error  // Asserted on data mismatch or extra data when CheckData is 1
);
  
  br_test_rate_control #(
      .Rate(Rate),
      .InitialDelay(InitialDelay),
      .Seed(Seed)
  ) br_test_rate_control (
      .clk,
      .rst,
      .enable(1'b1),
      .drive(push_ready),
      .ack(push_valid)
  );

  logic pushed;
  assign pushed = push_ready && push_valid;

  if (CheckData) begin : gen_check_data
    longint count;  // may exceed NumValues
    `BR_REGL(count, count + 1, pushed)
    assign done = count >= longint'(NumValues);

    // Expected data value for check
    logic [Width-1:0] expected_value;
    assign expected_value =
        UseCounterPattern   ? Width'(count) : 
        (count < longint'(NumValues)) ? expected_data[int'(count)] : 'x;
  
    always_ff @(posedge clk) begin
      if (rst) begin
        error <= 1'b0;
      end else if (pushed) begin
        if (done) begin
          $error("test_flow_sink %m: unexpected extra data at index %0d: %0h",
                 count, push_data);
          error <= 1'b1;
        end else if (push_data !== expected_value) begin
          $error("test_flow_sink %m: data mismatch at index %0d: expected %0h, got %0h",
                 count, expected_value, push_data);
          error <= 1'b1;
        end
      end
    end
  end else begin : gen_no_check_data
    assign done = 1'b0;
    assign error = 1'b0;
  end

endmodule
