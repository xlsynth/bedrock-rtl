// SPDX-License-Identifier: Apache-2.0


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

  // Round a value down to the nearest multiple of the alignment.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int align_down(input int value, input int alignment);
    // ri lint_check_waive WIDE_MULT
    return floor_div(value, alignment) * alignment;
  endfunction

  // Round a value up to the nearest multiple of the alignment.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int align_up(input int value, input int alignment);
    // ri lint_check_waive WIDE_MULT
    return ceil_div(value, alignment) * alignment;
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

  // Returns 2^x.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int exp2(input int x);
    // ri lint_check_waive VAR_SHIFT
    return 1 << x;
  endfunction

  // Rounds a value up to the nearest power of 2.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int round_up_to_power_of_2(input int value);
    return exp2($clog2(value));
  endfunction

endpackage : br_math
