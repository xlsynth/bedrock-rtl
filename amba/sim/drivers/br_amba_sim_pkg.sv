// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

package br_amba_sim_pkg;
  task automatic report_error(input string message, ref logic failed);
    failed = 1'b1;
    $error("%s", message);
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

endpackage : br_amba_sim_pkg
