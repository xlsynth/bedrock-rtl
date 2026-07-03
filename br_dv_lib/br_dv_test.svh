// SPDX-License-Identifier: Apache-2.0

class br_dv_test;
  local string name;
  local time   timeout;
  local int    error_count;
  local bit    vcd_dump_enabled;
  local bit    vcd_dump_started;
  local bit    run_done;
  local string vcd_dump_file;

  function new(input string name = "br_dv_test");
    this.name        = name;
    timeout          = 10000;
    error_count      = 0;
    vcd_dump_enabled = 1'b0;
    vcd_dump_started = 1'b0;
    run_done         = 1'b0;
    vcd_dump_file    = "br_dv_test.vcd";
  endfunction

  function void set_timeout(input time timeout);
    this.timeout = timeout;
  endfunction

  function void enable_vcd_dump(input string file_name = "br_dv_test.vcd");
    vcd_dump_enabled = 1'b1;
    vcd_dump_file = file_name;
  endfunction

  function void increment_errors(input int errors = 1);
    error_count += errors;
  endfunction

  virtual task test_body();
  endtask

  task start();
    run_done = 1'b0;
    start_vcd_dump();
    if (timeout != 0) begin
      fork
        begin
          #(timeout);
          if (!run_done) begin
            $fatal(1, "%s timeout after %0t", name, timeout);
          end
        end
      join_none
    end
  endtask

  task run();
    start();
    test_body();
    finish();
  endtask

  task start_vcd_dump();
    if (vcd_dump_enabled && !vcd_dump_started) begin
      $dumpfile(vcd_dump_file);
      $dumpvars(0);
      vcd_dump_started = 1'b1;
    end
  endtask

  task finish();
    run_done = 1'b1;
    if (error_count == 0) begin
      $display("TEST PASSED");
    end else begin
      $error("%s completed with %0d errors", name, error_count);
    end
    $finish;
  endtask
endclass
