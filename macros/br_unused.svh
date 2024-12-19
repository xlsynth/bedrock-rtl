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

`ifndef BR_UNUSED_SVH
`define BR_UNUSED_SVH

// Use this macro when a custom instance name suffix is required or desired.
// For example, use when __x__ is a complex expression (e.g., concatenation like {foo, bar}).
`define BR_UNUSED_NAMED(__name__, __x__) \
br_misc_unused #( \
    .Width($bits(__x__))) \
// ri lint_check_waive BLACKBOX \
br_misc_unused_``__name__ ( \
    .in(__x__) \
);

// Use this macro when __x__ is just a plain signal name.
`define BR_UNUSED(__x__) `BR_UNUSED_NAMED(__x__, __x__)

// Use for temporary unused signals.
// Intended to make temporary unused easier to find and resolve.
`define BR_UNUSED_TODO(__name__, __x__) `BR_UNUSED_NAMED(__name__, __x__)

`endif  // BR_UNUSED_SVH
