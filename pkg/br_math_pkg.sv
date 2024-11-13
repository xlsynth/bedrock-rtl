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
// Convenient helper functions for basic math operations.
package br_math;

  // Integer division with floor rounding.
  function automatic int floor_div(input int numerator, input int denominator);
    return numerator / denominator;
  endfunction

  // Integer division with ceil rounding.
  function automatic int ceil_div(input int numerator, input int denominator);
    return (numerator + denominator - 1) / denominator;
  endfunction

endpackage : br_math
