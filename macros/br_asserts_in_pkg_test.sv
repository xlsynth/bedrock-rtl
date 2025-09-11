// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

`include "br_asserts.svh"

// verilog_lint: waive package-filename
package br_asserts_test_pkg;
  localparam int Width = 4;
  `BR_ASSERT_STATIC_IN_PACKAGE(width_check_a, Width == 4)
endpackage : br_asserts_test_pkg

module br_asserts_in_pkg_test;
  // Reference the br_asserts_test_pkg so that the package is elaborated
  localparam int Width = br_asserts_test_pkg::Width;
  `BR_ASSERT_STATIC(width_check_a, Width == 4)
endmodule : br_asserts_in_pkg_test
