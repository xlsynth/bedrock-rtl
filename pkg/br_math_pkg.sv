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

// Bedrock-RTL Math Package
//
// Convenient helper functions for basic math operations. Only use these
// in elaboration-time logic.

// ri lint_check_waive FILE_NAME
package br_math;

  // Integer division with floor rounding.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int floor_div(input int numerator, input int denominator);
    // ri lint_check_waive DIVIDE
    return numerator / denominator;
  endfunction

  // Integer division with ceil rounding.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int ceil_div(input int numerator, input int denominator);
    // ri lint_check_waive ARITH_ARGS DIVIDE
    return (numerator + denominator - 1) / denominator;
  endfunction

  // Returns 1 if the value is a power of 2, 0 otherwise.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic bit is_power_of_2(input int value);
    return (value & (value - 1)) == 0;
  endfunction

  // Returns 1 if the value is even, 0 otherwise.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic bit is_even(input int value);
    return (value & 1'b1) == 0;
  endfunction

  // ceil(log_base(x)) using change-of-base formula. base must be a power-of-2.
  // Returns -1 on error.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int clogb(input int base, input int x);
    if ((base <= 1) || !is_power_of_2(base) || (x <= 0)) begin
      // ri lint_check_waive MULTI_RETURN
      return -1;  // Indicates an error
    end else begin
      return ceil_div($clog2(x), $clog2(base));
    end
  endfunction

  // If value > 1, returns $clog2(value). Otherwise, returns 1.
  // This function is useful for ensuring that address widths are at least 1.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int clamped_clog2(input int value);
    return (value <= 1) ? 1 : $clog2(value);
  endfunction

  // Returns the minimum of two integers.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int min2(input int a, input int b);
    return (a < b) ? a : b;
  endfunction

  // Returns the maximum of two integers.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int max2(input int a, input int b);
    return (a > b) ? a : b;
  endfunction

endpackage : br_math
