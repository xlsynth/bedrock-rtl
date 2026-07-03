// SPDX-License-Identifier: Apache-2.0

class br_dv_context;
  br_dv_test test;
  br_dv_component drivers[$];
  br_dv_component monitors[$];
  br_dv_component scoreboards[$];
  br_dv_sequence_base sequences[$];
  br_dv_agent agents[$];

  function new(input br_dv_test test);
    this.test = test;
  endfunction

  function void register(input br_dv_component component);
    br_dv_agent agent_handle;
    br_dv_sequence_base seq_handle;

    case (component.get_kind())
      BrDvDriver: drivers.push_back(component);
      BrDvMonitor: monitors.push_back(component);
      BrDvScoreboard: scoreboards.push_back(component);
      BrDvSequence: begin
        if (!$cast(seq_handle, component)) begin
          $fatal(1, "registered sequence is not a br_dv_sequence_base");
        end
        sequences.push_back(seq_handle);
      end
      BrDvAgent: begin
        if (!$cast(agent_handle, component)) begin
          $fatal(1, "registered agent is not a br_dv_agent");
        end
        agents.push_back(agent_handle);
      end
      default: $fatal(1, "unsupported br_dv_component kind");
    endcase
  endfunction

  task check(input logic condition, input string message = "Check failed");
    if (!condition) begin
      test.increment_errors();
      $error("%s", message);
    end
  endtask

  task check_integer(input int actual, input int expected, input string message = "Check failed");
    if (actual !== expected) begin
      test.increment_errors();
      $error("%s: Got %0d, Expected %0d", message, actual, expected);
    end
  endtask

  function bit any_seq_has_item();
    foreach (sequences[i]) begin
      if (sequences[i].has_item()) begin
        return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  function bit any_seq_is_running();
    foreach (sequences[i]) begin
      if (sequences[i].is_running()) begin
        return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  task wait_for_sequences(input br_dv_clk_rst_driver clk_rst_driver,
                          input int unsigned timeout_cycles,
                          input string timeout_message = "sequence timeout");
    int unsigned cycles;

    cycles = 0;
    while (any_seq_is_running() && (cycles < timeout_cycles)) begin
      clk_rst_driver.wait_cycles();
      cycles++;
    end
    check(!any_seq_is_running(), timeout_message);
  endtask
endclass
