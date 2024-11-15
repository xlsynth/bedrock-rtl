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

// Bedrock-RTL Signal Tie-off-to-One Driver
//
// Drives a signal to constant 1s and waives the corresponding lint errors internally.
// It is expected that downstream logic will be automatically constant-propagated by the
// synthesis tool.
//
// To automatically instantiate this at the width of local logic,
// users can opt to use the convenience macros defined in macros/br_tieoff.svh.
//
// We have separate modules for tie-to-zero and tie-to-one because
// lint tools may complain about multiple parameters per line when wrapped up in a macro.

module br_misc_tieoff_one #(
    parameter int Width = 1  // Must be at least 1
) (
    output logic [Width-1:0] out
);

  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  assign out = {Width{1'b1}};

endmodule : br_misc_tieoff_one
