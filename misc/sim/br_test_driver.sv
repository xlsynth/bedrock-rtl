// Basic test driver module that generates clock and reset for the testbench.
// Also contains helpful functions for test assertions

module br_test_driver #(
    parameter int ResetCycles   = 1,
    parameter int ClockPeriodNs = 10
) (
    output logic clk,
    output logic rst
);
  int error_count;

  initial clk = 1'b0;
  always #(ClockPeriodNs / 2) clk = ~clk;

  initial begin
    rst = 1'b1;
    error_count = 0;
  end

  // Wait a given number of clock cycles
  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  // Reset the DUT to prepare for a new test sequence
  task automatic reset_dut();
    $display("Resetting DUT");
    wait_cycles();
    rst = 1'b1;
    wait_cycles(ResetCycles);
    rst = 1'b0;
  endtask

  task automatic check(input logic condition, input string message = "Check failed");
    if (!condition) begin
      error_count++;
      $error("%s", message);
    end
  endtask

  task automatic check_integer(input int actual, input int expected,
                               input string message = "Check failed");
    if (actual !== expected) begin
      error_count++;
      $error("%s: Got %0d, Expected %0d", message, actual, expected);
    end
  endtask

  task automatic finish();
    // Finish simulation
    // TODO(zhemao, #130): Find a way to exit with failure if there were assertion failures.
    if (error_count == 0) begin
      $display("TEST PASSED");
    end else begin
      $display("Simulation failed with %0d errors.", error_count);
    end
    $finish;
  endtask

endmodule
