// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba_sim_pkg::*;
import br_amba_apb_sim_pkg::*;

// APB completer-side response driver.
//
// The driver owns only PREADY/PRDATA/PSLVERR and issues one directed response
// sequence per run call.
module br_amba_apb_completer_driver #(
    parameter int DataWidth = 32,
    parameter int TimeoutCycles = 100
) (
    input logic clk,
    input logic target_psel,
    input logic target_penable,

    output logic pready,
    output logic [DataWidth-1:0] prdata,
    output logic pslverr,
    output logic failed
);

  localparam logic [31:0] StallRdataBase = 32'h5a5a_0000;

  apb_response_t resp;
  event sample_tick;

  assign pready  = resp.ready;
  assign prdata  = DataWidth'(resp.rdata);
  assign pslverr = resp.slverr;

  clocking cb @(posedge clk);
    default input #1step;
    input target_psel;
    input target_penable;
  endclocking

  always begin
    @cb;
    ->sample_tick;
  end

  function automatic logic [31:0] stall_rdata(input int cycle);
    stall_rdata = StallRdataBase | cycle;
  endfunction

  task automatic init_idle();
    resp   = '0;
    failed = 1'b0;
  endtask

  task automatic wait_for_transfer_start();
    fork
      do @cb; while (!cb.target_psel);
      timeout(sample_tick, TimeoutCycles, "Timeout waiting for downstream APB transfer", failed);
    join_any
    disable fork;
  endtask

  task automatic wait_for_completion();
    fork
      do @cb; while (!(cb.target_psel && cb.target_penable && resp.ready));
      timeout(sample_tick, TimeoutCycles, "Timeout waiting for downstream APB completion", failed);
    join_any
    disable fork;
  endtask

  task automatic issue_response(input apb_response_t response);
    @(negedge clk);
    resp = response;
    @(negedge clk);
  endtask

  task automatic run_queue(input apb_response_t inputs[$], input apb_response_controls_t controls);
    apb_response_t response;

    for (int transaction = 0; transaction < controls.num_transactions; transaction++) begin
      if (transaction >= inputs.size()) begin
        failed = 1'b1;
        $error("APB completer response queue is shorter than requested transaction count");
        return;
      end
      response.ready = Pready1;
      response.rdata = inputs[transaction].rdata;
      response.slverr = inputs[transaction].slverr;
      resp = response;

      wait_for_transfer_start();
      if (failed) begin
        return;
      end
      for (int cycle = 0; cycle < controls.wait_cycles; cycle++) begin
        response.ready  = Pready0;
        response.rdata  = ApbDataWidth'(stall_rdata(cycle));
        response.slverr = Pslverr0;
        issue_response(response);
      end
      response.ready  = Pready1;
      response.rdata  = inputs[transaction].rdata;
      response.slverr = inputs[transaction].slverr;
      if (controls.wait_cycles != 0) begin
        @(negedge clk);
        resp = response;
      end
      wait_for_completion();
      if (failed) begin
        return;
      end
      @(negedge clk);
      resp = '0;
    end
  endtask

  task automatic run(input apb_response_t inputs, input apb_response_controls_t controls);
    apb_response_t response_queue[$];
    apb_response_t response;

    for (int transaction = 0; transaction < controls.num_transactions; transaction++) begin
      response.ready  = Pready1;
      response.rdata  = inputs.rdata + ApbDataWidth'(transaction);
      response.slverr = inputs.slverr;
      response_queue.push_back(response);
    end
    run_queue(response_queue, controls);
  endtask

endmodule : br_amba_apb_completer_driver
