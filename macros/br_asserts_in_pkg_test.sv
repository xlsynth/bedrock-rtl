// SPDX-License-Identifier: Apache-2.0


// Unit test for static assert macros involving packages

`timescale 1ns / 1ps

`include "br_asserts.svh"

// verilog_lint: waive package-filename
package br_asserts_test_pkg;
  localparam int Width = 4;
  `BR_ASSERT_STATIC_IN_PACKAGE(width_check_a, Width == 4)
`ifdef BR_ENABLE_FPV
  // This intentionally false assertion must elaborate under FPV, verifying that
  // BR_ASSERT_STATIC_IN_PACKAGE expands to a no-op when BR_ENABLE_FPV is set.
  `BR_ASSERT_STATIC_IN_PACKAGE(fp_static_asserts_disabled_a, 0)
`endif
endpackage : br_asserts_test_pkg

module br_asserts_in_pkg_test;
  // Reference the br_asserts_test_pkg so that the package is elaborated
  localparam int Width = br_asserts_test_pkg::Width;
  `BR_ASSERT_STATIC(width_check_a, Width == 4)
endmodule : br_asserts_in_pkg_test
