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

// Bedrock-RTL Flop-RAM (multi-read/multi-write) Tile
//
// A multi-read/multi-write flop-based RAM tile.
// The read and write ports may be clocked by different clocks.
// Read latency is zero cycles. Write latency is one cycle.
// By default, write-to-read latency is therefore one cycle.
// If the bypass is enabled, then the write-to-read latency is zero cycles, but
// at the cost of a combinational timing path from the write port to the read port.
// Bypassing is only permissible if the read and write clocks are the same.
//
// The tile does not handle address conflicts between write ports.
// The instantiating logic must ensure that two write ports do not
// write to the same address at the same time.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_ram_flops_multi_rw_tile #(
    parameter int NumWritePorts = 1,  // Must be at least 1
    parameter int NumReadPorts = 1,  // Must be at least 1
    parameter int Depth = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    // If 1, allow partial writes to the memory using the wr_word_en signal.
    // If 0, only full writes are allowed and wr_word_en is ignored.
    parameter bit EnablePartialWrite = 0,
    // The width of a word in the memory. This is the smallest unit of data that
    // can be written when partial write is enabled.
    // Must be at least 1 and at most Width.
    // Width must be evenly divisible by WordWidth.
    parameter int WordWidth = Width,
    // If 1, then if the read and write ports access the same address on the same cycle,
    // the write data is forwarded directly to the read data with zero delay.
    // Every write port will be bypassed to every read port if this is set.
    // If 0, then if the read and write ports access the same address on the same cycle,
    // then read data is the value stored in the memory prior to the write.
    parameter bit EnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset.
    parameter bit EnableReset = 0,
    // If 1, use structured mux2 gates for the read mux instead of relying on synthesis.
    // This is required if write and read clocks are different.
    parameter bit UseStructuredGates = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int NumWords = Width / WordWidth
) (
    input logic                                    wr_clk,
    // Synchronous active-high reset.
    // Reset is always used for assertions. Additionally used for logic only when EnableReset is 1.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic                                    wr_rst,
    input logic [NumWritePorts-1:0]                wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] wr_addr,
    input logic [NumWritePorts-1:0][    Width-1:0] wr_data,
    input logic [NumWritePorts-1:0][ NumWords-1:0] wr_word_en,

    // Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                   rd_clk,
    // Synchronous active-high reset.
    // Read reset is only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                   rd_rst,
    input  logic [NumReadPorts-1:0]                rd_addr_valid,
    input  logic [NumReadPorts-1:0][AddrWidth-1:0] rd_addr,
    output logic [NumReadPorts-1:0]                rd_data_valid,
    output logic [NumReadPorts-1:0][    Width-1:0] rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte1_a, Width >= 1)
  `BR_ASSERT_STATIC(no_bypass_with_structured_gates_a, !(EnableBypass && UseStructuredGates))

  `BR_ASSERT_CR_INTG(wr_addr_in_range_A, wr_valid |-> wr_addr < Depth, wr_clk, wr_rst)
  `BR_ASSERT_CR_INTG(rd_addr_in_range_A, rd_addr_valid |-> rd_addr < Depth, rd_clk, rd_rst)

  if (EnablePartialWrite) begin : gen_partial_write_intg_checks
    `BR_ASSERT_STATIC(word_width_in_range_a, (WordWidth >= 1) && (WordWidth <= Width))
    `BR_ASSERT_STATIC(width_divisible_by_word_width_a, (Width % WordWidth) == 0)
  end

  // If EnableBypass is 1 or UseStructuredGates is 0,
  // we must use the same clock for both read and write.
  if (EnableBypass || !UseStructuredGates) begin : gen_same_clock_check
    // ri lint_check_waive ALWAYS_COMB
    `BR_ASSERT_COMB_INTG(same_clock_a, wr_clk == rd_clk)
  end

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_wr_valid_a, !wr_valid)
    `BR_ASSERT_FINAL(final_not_rd_addr_valid_a, !rd_addr_valid)
    `BR_ASSERT_FINAL(final_not_rd_data_valid_a, !rd_data_valid)
  end

  if (NumWritePorts > 1) begin : gen_write_conflict_check
    for (genvar i = 0; i < (NumWritePorts - 1); i++) begin : gen_write_port
      for (genvar j = (i + 1); j < NumWritePorts; j++) begin : gen_write_port_conflict
        `BR_ASSERT_CR_INTG(no_write_conflict_a,
                           (wr_valid[i] && wr_valid[j]) |-> (wr_addr[i] != wr_addr[j]), wr_clk,
                           wr_rst)
      end
    end
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  if (!EnableReset) begin : gen_wr_reset_unused
    `BR_UNUSED(wr_rst)
  end

  if (!EnablePartialWrite) begin : gen_wr_word_en_unused
    `BR_UNUSED(wr_word_en)
  end

  // Storage flops are on the write clock but read asynchronously
  // from the read clock.
  logic [Depth-1:0][NumWords-1:0][WordWidth-1:0] mem;
  logic [NumWritePorts-1:0][Depth-1:0] wr_addr_onehot;
  // Need the transpose of wr_addr_onehot so that we can
  // group by depth for the storage flop write-enables.
  logic [Depth-1:0][NumWritePorts-1:0] wr_addr_onehot_transpose;

  // Write address decoding
  for (genvar port = 0; port < NumWritePorts; port++) begin : gen_wr_addr_onehot
    br_enc_bin2onehot #(
        .NumValues(Depth)
    ) br_enc_bin2onehot_inst (
        .clk(wr_clk),  // ri lint_check_waive SAME_CLOCK_NAME
        .rst(wr_rst),
        .in_valid(wr_valid[port]),
        .in(wr_addr[port]),
        .out(wr_addr_onehot[port])
    );

    for (genvar i = 0; i < Depth; i++) begin : gen_wr_addr_onehot_transpose
      assign wr_addr_onehot_transpose[i][port] = wr_addr_onehot[port][i];
    end
  end

  for (genvar i = 0; i < Depth; i++) begin : gen_storage_flops
    logic mem_wr_en;
    logic [Width-1:0] mem_wr_data;

    // Select the write data based on which write port
    // has the matching address if any.
    if (NumWritePorts > 1) begin : gen_mux_onehot_wr_data
      br_mux_onehot #(
          .NumSymbolsIn(NumWritePorts),
          .SymbolWidth (Width)
      ) br_mux_onehot_wr_data (
          .select(wr_addr_onehot_transpose[i]),
          .in(wr_data),
          .out(mem_wr_data)
      );
    end else begin : gen_single_port_wr_data
      assign mem_wr_data = wr_data;
    end

    assign mem_wr_en = |wr_addr_onehot_transpose[i];

    if (EnablePartialWrite) begin : gen_partial_write
      logic [NumWords-1:0][WordWidth-1:0] mem_wr_data_words;
      logic [NumWords-1:0] mem_wr_word_en;

      assign mem_wr_data_words = mem_wr_data;

      // Select the word-enable to use for this row.
      if (NumWritePorts > 1) begin : gen_mux_onehot_wr_word_en
        br_mux_onehot #(
            .NumSymbolsIn(NumWritePorts),
            .SymbolWidth (NumWords)
        ) br_mux_onehot_wr_word_en (
            .select(wr_addr_onehot_transpose[i]),
            .in(wr_word_en),
            .out(mem_wr_word_en)
        );
      end else begin : gen_single_port_wr_word_en
        assign mem_wr_word_en = wr_word_en;
      end

      for (genvar word = 0; word < NumWords; word++) begin : gen_partial_write_flops
        if (EnableReset) begin : gen_reset
          `BR_REGLX(mem[i][word], mem_wr_data_words[word], mem_wr_en && mem_wr_word_en[word],
                    wr_clk, wr_rst)
        end else begin : gen_no_reset
          `BR_REGLNX(mem[i][word], mem_wr_data_words[word], mem_wr_en && mem_wr_word_en[word],
                     wr_clk)
        end
      end
    end else begin : gen_no_partial_write
      if (EnableReset) begin : gen_reset
        `BR_REGLX(mem[i], mem_wr_data, mem_wr_en, wr_clk, wr_rst)
      end else begin : gen_no_reset
        `BR_REGLNX(mem[i], mem_wr_data, mem_wr_en, wr_clk)
      end
    end
  end

  // Read ports
  assign rd_data_valid = rd_addr_valid;

  for (genvar rport = 0; rport < NumReadPorts; rport++) begin : gen_read_port
    logic [Width-1:0] rd_data_mem;

    br_mux_bin #(
        .NumSymbolsIn(Depth),
        .SymbolWidth(Width),
        .UseStructuredGates(UseStructuredGates)
    ) br_mux_bin_inst (
        .select(rd_addr[rport]),
        .in(mem),
        .out(rd_data_mem),
        .out_valid()
    );

    if (EnableBypass) begin : gen_bypass
      logic [Width-1:0] rd_data_bypass;
      logic [NumWritePorts-1:0] wr_addr_match;

      for (genvar wport = 0; wport < NumWritePorts; wport++) begin : gen_wr_addr_match
        assign wr_addr_match[wport] = wr_valid[wport] && (wr_addr[wport] == rd_addr[rport]);
      end

      if (NumWritePorts > 1) begin : gen_bypass_mux
        br_mux_onehot #(
            .NumSymbolsIn(NumWritePorts),
            .SymbolWidth (Width)
        ) br_mux_onehot_rd_data_bypass (
            .select(wr_addr_match),
            .in(wr_data),
            .out(rd_data_bypass)
        );
      end else begin : gen_bypass_passthru
        assign rd_data_bypass = wr_data;
      end

      assign rd_data[rport] = (|wr_addr_match) ? rd_data_bypass : rd_data_mem;
    end else begin : gen_no_bypass
      assign rd_data[rport] = rd_data_mem;
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(zero_read_latency_A, rd_addr_valid |-> rd_data_valid, rd_clk, rd_rst)
`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  if (EnableBypass) begin : gen_bypass_impl_checks
    for (
        genvar wport = 0; wport < NumWritePorts; wport++
    ) begin : gen_bypass_write_to_read_check_wport
      for (
          genvar rport = 0; rport < NumReadPorts; rport++
      ) begin : gen_bypass_write_to_read_check_rport
        logic write_matches_read;

        assign write_matches_read =
            (wr_valid[wport] && rd_addr_valid[rport] && (wr_addr[wport] == rd_addr[rport]));

        if (EnablePartialWrite) begin : gen_partial_write_bypass_impl_checks
          for (
              genvar word = 0; word < NumWords; word++
          ) begin : gen_partial_write_bypass_impl_checks_word
            logic [WordWidth-1:0] rd_data_word;
            logic [WordWidth-1:0] wr_data_word;

            assign rd_data_word = rd_data[rport][word*WordWidth+:WordWidth];
            assign wr_data_word = wr_data[wport][word*WordWidth+:WordWidth];

            `BR_ASSERT_CR_IMPL(bypass_write_to_read_zero_cycles_A,
                               (write_matches_read && wr_word_en[wport][word])
                               |->
                               (rd_data_valid[rport] && rd_data_word == wr_data_word),
                               rd_clk, rd_rst)
          end
        end else begin : gen_full_write_bypass_impl_checks
          `BR_ASSERT_CR_IMPL(
              bypass_write_to_read_zero_cycles_A,
              write_matches_read |-> (rd_data_valid[rport] && rd_data[rport] == wr_data[wport]),
              rd_clk, rd_rst)
        end
      end
    end
  end
`endif
`endif

endmodule : br_ram_flops_multi_rw_tile
