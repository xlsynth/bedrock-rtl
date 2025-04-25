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

// Unit test for br_ecc_secded_pkg.sv

`include "br_asserts_internal.svh"

// ri lint_check_waive NO_OUTPUT
module br_ecc_secded_pkg_tb;

  // Test cases for get_max_message_width function
  `BR_ASSERT_STATIC(get_max_message_width_4_a, br_ecc_secded::_get_max_message_width(4) == 4)
  `BR_ASSERT_STATIC(get_max_message_width_5_a, br_ecc_secded::_get_max_message_width(5) == 11)
  `BR_ASSERT_STATIC(get_max_message_width_6_a, br_ecc_secded::_get_max_message_width(6) == 26)
  `BR_ASSERT_STATIC(get_max_message_width_7_a, br_ecc_secded::_get_max_message_width(7) == 57)
  `BR_ASSERT_STATIC(get_max_message_width_8_a, br_ecc_secded::_get_max_message_width(8) == 120)
  `BR_ASSERT_STATIC(get_max_message_width_9_a, br_ecc_secded::_get_max_message_width(9) == 247)
  `BR_ASSERT_STATIC(get_max_message_width_10_a, br_ecc_secded::_get_max_message_width(10) == 502)
  `BR_ASSERT_STATIC(get_max_message_width_11_a, br_ecc_secded::_get_max_message_width(11) == 1013)
  `BR_ASSERT_STATIC(get_max_message_width_12_a, br_ecc_secded::_get_max_message_width(12) == 2036)

  // Test cases for get_message_width function
  `BR_ASSERT_STATIC(get_message_width_4_4_a, br_ecc_secded::get_message_width(4, 4) == 4)
  `BR_ASSERT_STATIC(get_message_width_15_6_a, br_ecc_secded::get_message_width(15, 6) == 16)
  `BR_ASSERT_STATIC(get_message_width_16_6_a, br_ecc_secded::get_message_width(16, 6) == 16)
  `BR_ASSERT_STATIC(get_message_width_17_6_a, br_ecc_secded::get_message_width(17, 6) == 26)

  // Test cases for get_parity_width function
  `BR_ASSERT_STATIC(get_parity_width_32_a, br_ecc_secded::get_parity_width(32) == 7)
  `BR_ASSERT_STATIC(get_parity_width_63_a, br_ecc_secded::get_parity_width(63) == 8)
  `BR_ASSERT_STATIC(get_parity_width_64_a, br_ecc_secded::get_parity_width(64) == 8)
  `BR_ASSERT_STATIC(get_parity_width_120_a, br_ecc_secded::get_parity_width(120) == 8)
  `BR_ASSERT_STATIC(get_parity_width_121_a, br_ecc_secded::get_parity_width(121) == 9)

  // Combo message and parity width functions
  `BR_ASSERT_STATIC(data_width_4_a, br_ecc_secded::get_message_width(
                    4, br_ecc_secded::get_parity_width(4)) == 4)
  `BR_ASSERT_STATIC(data_width_15_a, br_ecc_secded::get_message_width(
                    15, br_ecc_secded::get_parity_width(15)) == 16)
  `BR_ASSERT_STATIC(data_width_16_a, br_ecc_secded::get_message_width(
                    16, br_ecc_secded::get_parity_width(16)) == 16)
  `BR_ASSERT_STATIC(data_width_17_a, br_ecc_secded::get_message_width(
                    17, br_ecc_secded::get_parity_width(17)) == 26)
endmodule : br_ecc_secded_pkg_tb
