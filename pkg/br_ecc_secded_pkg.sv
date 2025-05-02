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

// Bedrock-RTL ECC Package
//
// Convenient helper functions for instantiating error-correcting codes. Only use these
// in elaboration-time logic.
//
// References:
// [1] https://ieeexplore.ieee.org/abstract/document/5391627
// [2] https://arxiv.org/pdf/0803.1217

// ri lint_check_waive FILE_NAME
package br_ecc_secded;

  // Internal helper function for get_message_width. Don't use this directly.
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int _get_max_message_width(input int parity_width);
    return br_math::exp2(parity_width - 1) - parity_width;
  endfunction : _get_max_message_width

  // Given a data width and a parity width, returns the smallest RTL-supported message width that can fit the data.
  // Only use this function in elaboration-time logic.
  //
  // This function does not check that the data width and parity width are actually within the ranges
  // supported by the RTL. Rely on the RTL's static assertions for that.
  //
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int get_message_width(input int data_width, input int parity_width);
    return br_math::min2(br_math::round_up_to_power_of_2(data_width),
                         _get_max_message_width(parity_width));
  endfunction : get_message_width

  // Given a message (or data) width, returns the smallest parity width that can fit the message for any SECDED code.
  // Only use this function in elaboration-time logic.
  // ri lint_check_off MULTI_RETURN
  // ri lint_check_off CONST_BASE
  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int get_parity_width(input int message_width);
    // No closed form equation. As per reference [2], we have:
    //
    //   r >= 1 + log2(k + r)
    //
    // where k is the message width and r is the parity width.
    //
    // We implement a lookup table for the cases that are supported by the RTL.
    if (message_width == 4) begin
      return 4;
    end else if (message_width >= 5 && message_width <= 11) begin
      return 5;
    end else if (message_width >= 12 && message_width <= 26) begin
      return 6;
    end else if (message_width >= 27 && message_width <= 57) begin
      return 7;
    end else if (message_width >= 58 && message_width <= 120) begin
      return 8;
    end else if (message_width >= 121 && message_width <= 247) begin
      return 9;
    end else if (message_width >= 248 && message_width <= 502) begin
      return 10;
    end else if (message_width >= 503 && message_width <= 1013) begin
      return 11;
    end else if (message_width >= 1014 && message_width <= 1024) begin
      return 12;
    end else begin
      // Unimplemented
      return 0;
    end
  endfunction : get_parity_width
  // ri lint_check_on CONST_BASE
  // ri lint_check_on MULTI_RETURN

endpackage : br_ecc_secded
