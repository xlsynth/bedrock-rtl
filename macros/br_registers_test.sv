// SPDX-License-Identifier: Apache-2.0

`include "br_registers.svh"

// Elaboration fixture for every register macro, including scalar NOSCAN outputs.
module br_registers_test (
    input logic clk,
    input logic rst,
    input logic arst,
    input logic custom_clk,
    input logic custom_rst,
    input logic custom_arst,
    input logic [7:0] data,
    input logic enable,
    output logic [7:0] regn_q,
    output logic [7:0] regln_q,
    output logic [7:0] reg_q,
    output logic [7:0] regl_q,
    output logic [7:0] regi_q,
    output logic [7:0] regli_q,
    output logic [7:0] rega_q,
    output logic [7:0] regal_q,
    output logic [7:0] regai_q,
    output logic [7:0] regali_q,
    output logic [7:0] regax_q,
    output logic [7:0] regalx_q,
    output logic [7:0] regaix_q,
    output logic [7:0] regalix_q,
    output logic [7:0] regx_q,
    output logic [7:0] reglx_q,
    output logic [7:0] regix_q,
    output logic [7:0] reglix_q,
    output logic [7:0] regnx_q,
    output logic [7:0] reglnx_q,
    output logic [7:0] regnx_noscan_q,
    output logic [7:0] regx_noscan_q,
    output logic [7:0] reglx_noscan_q,
    output logic [7:0] regax_noscan_q,
    output logic [7:0] regalx_noscan_q,
    output logic regnx_noscan_scalar_q,
    output logic regx_noscan_scalar_q,
    output logic reglx_noscan_scalar_q,
    output logic regax_noscan_scalar_q,
    output logic regalx_noscan_scalar_q
);

  `BR_REGN(regn_q, data)
  `BR_REGLN(regln_q, data, enable)

  `BR_REG(reg_q, data)
  `BR_REGL(regl_q, data, enable)
  `BR_REGI(regi_q, data, 8'hA5)
  `BR_REGLI(regli_q, data, enable, 8'hA5)

  `BR_REGA(rega_q, data)
  `BR_REGAL(regal_q, data, enable)
  `BR_REGAI(regai_q, data, 8'hA5)
  `BR_REGALI(regali_q, data, enable, 8'hA5)

  `BR_REGAX(regax_q, data, custom_clk, custom_arst)
  `BR_REGALX(regalx_q, data, enable, custom_clk, custom_arst)
  `BR_REGAIX(regaix_q, data, 8'hA5, custom_clk, custom_arst)
  `BR_REGALIX(regalix_q, data, enable, 8'hA5, custom_clk, custom_arst)

  `BR_REGX(regx_q, data, custom_clk, custom_rst)
  `BR_REGLX(reglx_q, data, enable, custom_clk, custom_rst)
  `BR_REGIX(regix_q, data, 8'hA5, custom_clk, custom_rst)
  `BR_REGLIX(reglix_q, data, enable, 8'hA5, custom_clk, custom_rst)
  `BR_REGNX(regnx_q, data, custom_clk)
  `BR_REGLNX(reglnx_q, data, enable, custom_clk)

  `BR_REGNX_NOSCAN(regnx_noscan_q, data, custom_clk)
  `BR_REGX_NOSCAN(regx_noscan_q, data, custom_clk, custom_rst)
  `BR_REGLX_NOSCAN(reglx_noscan_q, data, enable, custom_clk, custom_rst)
  `BR_REGAX_NOSCAN(regax_noscan_q, data, custom_clk, custom_arst)
  `BR_REGALX_NOSCAN(regalx_noscan_q, data, enable, custom_clk, custom_arst)

  `BR_REGNX_NOSCAN(regnx_noscan_scalar_q, data[0], custom_clk)
  `BR_REGX_NOSCAN(regx_noscan_scalar_q, data[0], custom_clk, custom_rst)
  `BR_REGLX_NOSCAN(reglx_noscan_scalar_q, data[0], enable, custom_clk, custom_rst)
  `BR_REGAX_NOSCAN(regax_noscan_scalar_q, data[0], custom_clk, custom_arst)
  `BR_REGALX_NOSCAN(regalx_noscan_scalar_q, data[0], enable, custom_clk, custom_arst)

endmodule : br_registers_test
