// Copyright 2024-2025 The Bedrock-RTL Authors
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
// Convenient helper functions for constructing error-correcting codes. Only use these
// in elaboration-time logic.

// ri lint_check_waive FILE_NAME
package br_ecc;

  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int get_max_message_width(input int parity_width);
    return br_math::exp2(parity_width - 1) - parity_width;
  endfunction : get_max_message_width

  // ri lint_check_waive TWO_STATE_TYPE
  function automatic int get_message_width(input int message_width, input int parity_width);
    return br_math::is_power_of_2(message_width) ? message_width :
        get_max_message_width(parity_width);
  endfunction : get_message_width

endpackage : br_ecc
