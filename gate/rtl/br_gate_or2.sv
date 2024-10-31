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

// Bedrock-RTL 2-Input OR Gate
//
// The output is the logical OR of the two inputs.

module br_gate_or2 (
    input  logic in1,
    input  logic in2,
    output logic out
);

  br_gatelib__or2 gate (
      .in1,
      .in2,
      .out
  );

endmodule : br_gate_or2
