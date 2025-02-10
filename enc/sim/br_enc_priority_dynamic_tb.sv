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

// Bedrock-RTL Dynamic Priority Encoder Testbench
//
// Since this is a purely combinational block with just one input,
// we can just exhaustively test all possible input values.

module br_enc_priority_dynamic_tb;
  parameter int NumRequesters = 8;
  parameter int NumResults = 3;
  localparam int MaxInValue = (2 ** NumRequesters) - 1;

  logic clk;
  logic rst;
  logic [NumRequesters-1:0] in;
  logic [NumRequesters-1:0] lowest_prio;
  logic [NumResults-1:0][NumRequesters-1:0] out;
  logic [NumResults-1:0][NumRequesters-1:0] expected_out;

  br_enc_priority_dynamic #(
      .NumRequesters(NumRequesters),
      .NumResults(NumResults)
  ) dut (
      .clk,
      .rst,
      .in,
      .lowest_prio,
      .out
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [NumResults-1:0][NumRequesters-1:0] calc_expected_out(
      logic [NumRequesters-1:0] in, int lp);
    int hp;
    int res_idx;
    logic [NumResults-1:0][NumRequesters-1:0] fout;

    hp = (lp + 1) % NumRequesters;
    fout = '0;
    res_idx = 0;
    for (int i = 0; i < NumRequesters; i++) begin
      int j = (hp + i) % NumRequesters;

      if (in[j]) begin
        fout[res_idx][j] = 1;
        res_idx++;

        if (res_idx == NumResults) break;
      end
    end

    return fout;
  endfunction

  initial begin
    in = '0;
    lowest_prio = 1;

    td.reset_dut();

    @(negedge clk);
    for (int i = 0; i < NumRequesters; i++) begin
      lowest_prio = 1 << i;

      for (int j = 0; j < MaxInValue; j++) begin
        in = j;
        @(posedge clk);
        expected_out = calc_expected_out(in, i);
        td.check_integer(out, expected_out, $sformatf(
                         "Out does not match expected at lp=%d, in=%0x", i, j));
        @(negedge clk);
      end
    end

    td.finish();
  end
endmodule
