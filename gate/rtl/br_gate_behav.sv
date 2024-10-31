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

// Bedrock-RTL Gate Library Behavioral Models
//
// This file contains behavioral models for the Bedrock-RTL gate library. This
// file is expected to be branched for each vendor technology and behavioral
// models should be replaced with vendor-specific standard cells. Only one
// version of the gatelib should be included in the design filelist.

// verilog_lint: waive-start module-filename
// ri lint_check_off ONE_PER_FILE FILE_NAME

// 2-input AND gate
module br_gate_and2 (
    input  logic in1,
    input  logic in2,
    output logic out
);

  assign out = in1 & in2;

endmodule : br_gate_and2

// 2-input OR gate
module br_gate_or2 (
    input  logic in1,
    input  logic in2,
    output logic out
);

  assign out = in1 | in2;

endmodule : br_gate_or2

// verilog_lint: waive-stop module-filename
// ri lint_check_on ONE_PER_FILE FILE_NAME
