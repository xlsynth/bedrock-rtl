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

// Bedrock-RTL Unused Signal Sink
//
// Sinks an unused signal and waives the corresponding lint errors internally.
// It is expected that this logic will be automatically removed by the
// synthesis tool.
//
// To automatically instantiate this at the width of local logic,
// users can opt to use the `BR_UNUSED(signal) or `BR_UNUSED_NAMED(name, expression)
// convenience macros defined in macros/br_unused.svh.

// ri lint_check_waive EMPTY_MOD NO_OUTPUT
module br_misc_unused #(
    parameter int Width = 1  // Must be at least 1
) (
    input logic [Width-1:0] in
);

  logic unused;  // ri lint_check_waive NOT_READ
  assign unused = |in;

endmodule : br_misc_unused
