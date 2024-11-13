// Copyright 2024 The Bedrock-RTL Authors
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

// Unit test for br_math_pkg.sv

`include "br_asserts_internal.svh"

module br_math_pkg_tb;

  // Test cases for floor_div function
  `BR_ASSERT_STATIC(floordiv_10_5_a, br_math::floor_div(10, 5) == 2)
  `BR_ASSERT_STATIC(floordiv_10_4_a, br_math::floor_div(10, 4) == 2)
  `BR_ASSERT_STATIC(floordiv_7_3_a, br_math::floor_div(7, 3) == 2)
  `BR_ASSERT_STATIC(floordiv_9_2_a, br_math::floor_div(9, 2) == 4)
  `BR_ASSERT_STATIC(floordiv_0_1_a, br_math::floor_div(0, 1) == 0)
  `BR_ASSERT_STATIC(floordiv_neg5_2_a, br_math::floor_div(-5, 2) == -2)

  // Test cases for ceil_div function
  `BR_ASSERT_STATIC(ceildiv_10_5_a, br_math::ceil_div(10, 5) == 2)
  `BR_ASSERT_STATIC(ceildiv_10_4_a, br_math::ceil_div(10, 4) == 3)
  `BR_ASSERT_STATIC(ceildiv_7_3_a, br_math::ceil_div(7, 3) == 3)
  `BR_ASSERT_STATIC(ceildiv_9_2_a, br_math::ceil_div(9, 2) == 5)
  `BR_ASSERT_STATIC(ceildiv_0_1_a, br_math::ceil_div(0, 1) == 0)
  `BR_ASSERT_STATIC(ceildiv_neg5_2_a, br_math::ceil_div(-5, 2) == -2)

  // Test cases for is_power_of_2 function
  `BR_ASSERT_STATIC(ispowerof2_0_a, br_math::is_power_of_2(0) == 1)
  `BR_ASSERT_STATIC(ispowerof2_1_a, br_math::is_power_of_2(1) == 1)
  `BR_ASSERT_STATIC(ispowerof2_2_a, br_math::is_power_of_2(2) == 1)
  `BR_ASSERT_STATIC(ispowerof2_128_a, br_math::is_power_of_2(128) == 1)

  `BR_ASSERT_STATIC(ispowerof2_m0_a, br_math::is_power_of_2(-0) == 1)
  `BR_ASSERT_STATIC(ispowerof2_m1_a, br_math::is_power_of_2(-1) == 1)
  `BR_ASSERT_STATIC(ispowerof2_m2_a, br_math::is_power_of_2(-2) == 1)
  `BR_ASSERT_STATIC(ispowerof2_m128_a, br_math::is_power_of_2(-128) == 1)

  `BR_ASSERT_STATIC(not_ispowerof2_3_a, br_math::is_power_of_2(3) == 0)
  `BR_ASSERT_STATIC(not_ispowerof2_7_a, br_math::is_power_of_2(7) == 0)
  `BR_ASSERT_STATIC(not_ispowerof2_26_a, br_math::is_power_of_2(26) == 0)
  `BR_ASSERT_STATIC(not_ispowerof2_27_a, br_math::is_power_of_2(27) == 0)

  `BR_ASSERT_STATIC(not_ispowerof2_m3_a, br_math::is_power_of_2(-3) == 0)
  `BR_ASSERT_STATIC(not_ispowerof2_m7_a, br_math::is_power_of_2(-7) == 0)
  `BR_ASSERT_STATIC(not_ispowerof2_m26_a, br_math::is_power_of_2(-26) == 0)
  `BR_ASSERT_STATIC(not_ispowerof2_m27_a, br_math::is_power_of_2(-27) == 0)

endmodule : br_math_pkg_tb
