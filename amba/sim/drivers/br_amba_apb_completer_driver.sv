// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba_apb_sim_pkg::*;

// APB completer-side response driver.
//
// The driver owns only PREADY/PRDATA/PSLVERR and issues one directed response
// sequence per run call.
module br_amba_apb_completer_driver #(
    parameter int TimeoutCycles = 100
) (
    input logic clk,
    input logic target_psel,
    input logic target_penable,

    output logic pready,
    output logic [31:0] prdata,
    output logic pslverr
);

  localparam logic [31:0] StallRdataBase = 32'h5a5a_0000;

  apb_response_t resp;

  assign pready  = resp.ready;
  assign prdata  = resp.rdata;
  assign pslverr = resp.slverr;

  function automatic logic [31:0] stall_rdata(input int cycle);
    stall_rdata = StallRdataBase | cycle;
  endfunction

  task automatic init_idle();
    resp = '0;
  endtask

  task automatic wait_for_access();
    int timeout = 0;

    @(posedge clk);
    while (!(target_psel && target_penable) && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    if (!(target_psel && target_penable)) begin
      $error("Timeout waiting for downstream APB access");
    end
  endtask

  task automatic issue_response(input apb_response_t response);
    @(negedge clk);
    resp = response;
    @(negedge clk);
  endtask

  task automatic run(input apb_response_t inputs, input apb_response_controls_t controls);
    apb_response_t response;

    for (int transaction = 0; transaction < controls.num_transactions; transaction++) begin
      wait_for_access();
      for (int cycle = 0; cycle < controls.wait_cycles; cycle++) begin
        response.ready  = Pready0;
        response.rdata  = stall_rdata(cycle);
        response.slverr = Pslverr0;
        issue_response(response);
      end
      response.ready  = Pready1;
      response.rdata  = inputs.rdata + 32'(transaction);
      response.slverr = inputs.slverr;
      issue_response(response);
      resp = '0;
    end
  endtask

endmodule : br_amba_apb_completer_driver
