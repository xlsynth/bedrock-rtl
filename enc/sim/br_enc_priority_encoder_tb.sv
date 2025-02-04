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

// Bedrock-RTL Priority Encoder Testbench
//
// Since this is a purely combinational block with just one input,
// we can just exhaustively test all possible input values.

module br_enc_priority_encoder_tb;
  parameter int NumRequesters = 8;
  parameter int NumResults = 3;
  parameter bit MsbHighestPriority = 0;
  localparam int MaxInValue = (2 ** NumRequesters) - 1;

  logic clk;
  logic rst;

  logic [NumRequesters-1:0] in;
  logic [NumResults-1:0][NumRequesters-1:0] out;

  br_test_driver driver (
      .clk,
      .rst
  );

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters),
      .NumResults(NumResults),
      .MsbHighestPriority(MsbHighestPriority)
  ) dut (
      .clk,
      .rst,
      .in,
      .out
  );

  function automatic logic [NumResults-1:0][NumRequesters-1:0] calc_expected_out(input int fin);
    int res_idx = 0;
    logic [NumResults-1:0][NumRequesters-1:0] fout;

    fout = '0;
    if (MsbHighestPriority) begin
      for (int i = NumRequesters - 1; i >= 0; i--) begin
        // Once we find an input bit set, just set it on the current
        // output and then move on to the next output.
        if (fin[i]) begin
          fout[res_idx][i] = 1;
          res_idx++;
          // We're done once we've found a set bit for each output.
          if (res_idx == NumResults) break;
        end
      end
    end else begin
      for (int i = 0; i < NumRequesters; i++) begin
        // Once we find an input bit set, just set it on the current
        // output and then move on to the next output.
        if (fin[i]) begin
          fout[res_idx][i] = 1;
          res_idx++;
          // We're done once we've found a set bit for each output.
          if (res_idx == NumResults) break;
        end
      end
    end
    return fout;
  endfunction

  initial begin
    logic [NumResults-1:0][NumRequesters-1:0] expected_out;

    in = '0;

    driver.reset_dut();

    // Exhaustively test all possible input values
    for (int i = 0; i <= MaxInValue; i++) begin
      @(negedge clk);
      in = i;
      expected_out = calc_expected_out(i);
      @(posedge clk);
      driver.check_integer(out, expected_out, $sformatf("Output mismatch for input %0d", i));
    end

    @(negedge clk);

    driver.finish();
  end

endmodule
