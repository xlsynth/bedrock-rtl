// Copyright 2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Unit test for static assert macros involving packages

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
