// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_sim_pkg;
  localparam int BrAmbaSimMaxCheckWidth = 1024;

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
    failed = 1'b1;
    $error("%s", message);
  endtask

  function automatic int get_random_stall_cycles(input int max_stall_cycles);
    if (max_stall_cycles == 0) begin
      return 0;
    end
    return int'($urandom_range(max_stall_cycles, 0));
  endfunction

endpackage : br_amba_sim_pkg
