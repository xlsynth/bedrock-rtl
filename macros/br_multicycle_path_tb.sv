// SPDX-License-Identifier: Apache-2.0


// Unit test for br_multicycle_path.svh macros

`include "br_multicycle_path.svh"

module br_multicycle_path_tb ();  // ri lint_check_waive NO_OUTPUT

  wire clk = 1'b0;  // ri lint_check_waive CONST_ASSIGN
  wire rst = 1'b0;  // ri lint_check_waive CONST_ASSIGN

  wire [1:0] in = 2'b01;  // ri lint_check_waive CONST_ASSIGN
  logic [1:0] out;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic [1:0] reset_only_out;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ

  `BR_MCP(2, in, out)
  `BR_RESET_ONLY_MCP(2, in, reset_only_out)

  wire foo = 1'b0;  // ri lint_check_waive CONST_ASSIGN
  wire bar = 1'b1;  // ri lint_check_waive CONST_ASSIGN
  logic [1:0] named_out;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ
  logic [1:0] named_reset_only_out;  // ri lint_check_waive NOT_READ HIER_NET_NOT_READ

  `BR_MCP_NAMED(named_path, 2, {foo, bar}, named_out)
  `BR_RESET_ONLY_MCP_NAMED(named_reset_only_path, 2, {foo, bar}, named_reset_only_out)

endmodule : br_multicycle_path_tb
