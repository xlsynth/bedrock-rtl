// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for BR_GATE_CDC_RST_SYNC macro expansion.

`include "br_gates.svh"

module br_gates_cdc_rst_sync_fpv_repro (
    input  logic clk,
    input  logic arst,
    output logic srst
);

  `BR_GATE_CDC_RST_SYNC(srst, arst, clk)

endmodule : br_gates_cdc_rst_sync_fpv_repro
