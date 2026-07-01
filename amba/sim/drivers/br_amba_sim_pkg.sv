// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_sim_pkg;
`ifdef BR_AMBA_SIM_MAX_CHECK_WIDTH
  parameter int BrAmbaSimMaxCheckWidth = `BR_AMBA_SIM_MAX_CHECK_WIDTH;
`else
  parameter int BrAmbaSimMaxCheckWidth = 1024;
`endif

  task automatic report_error(input string message, ref logic failed);
    failed = 1'b1;
    $error("%s", message);
  endtask

  task automatic check_eq(input logic [BrAmbaSimMaxCheckWidth-1:0] actual,
                          input logic [BrAmbaSimMaxCheckWidth-1:0] expected, input string message,
                          ref logic failed);
    if (actual !== expected) begin
      failed = 1'b1;
      $error("%s: expected 0x%0h got 0x%0h", message, expected, actual);
    end
  endtask

  task automatic timeout(input event tick, input int cycles, input string message,
                         ref logic failed);
    repeat (cycles) @tick;
    report_error(message, failed);
  endtask

  function automatic int get_random_stall_cycles(input int max_stall_cycles);
    if (max_stall_cycles == 0) begin
      return 0;
    end
    return int'($urandom_range(max_stall_cycles, 0));
  endfunction

  function automatic logic [BrAmbaSimMaxCheckWidth-1:0] get_random_bits(input int width);
    get_random_bits = '0;

    if (width > BrAmbaSimMaxCheckWidth) begin
      $fatal(1, "Requested %0d random bits exceeds common sim helper width %0d", width,
             BrAmbaSimMaxCheckWidth);
    end

    for (int offset = 0; offset < width; offset += 32) begin
      logic [31:0] word = $urandom();

      for (int bit_idx = 0; bit_idx < 32 && offset + bit_idx < width; bit_idx++) begin
        get_random_bits[offset+bit_idx] = word[bit_idx];
      end
    end
  endfunction

endpackage : br_amba_sim_pkg
