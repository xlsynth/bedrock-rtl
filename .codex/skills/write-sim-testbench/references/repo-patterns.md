# Bedrock-RTL Simulation Testbench Patterns

Use this reference for concrete local patterns after loading the `write-sim-testbench` skill.

## Core Helpers

- `misc/sim/br_test_driver.sv`: single-clock helper with `clk`, `rst`, `wait_cycles`, `reset_dut`, `check`, `check_integer`, and `finish`. Most new simple benches should use this.
- `misc/sim/br_test_rate_control.sv`: probabilistic hold-until-accepted drive signal with `Rate`, `InitialDelay`, and `Seed`.
- `flow/sim/br_flow_test_driver.sv` and `flow/sim/br_flow_test_sink.sv`: reusable ready/valid endpoints built on `br_test_rate_control`.
- `fifo/sim/br_fifo_test_harness.sv`: single FIFO fill/full/drain/interleaved harness with expected-data checks.
- `fifo/sim/br_fifo_shared_test_harness.sv`: shared FIFO queue scoreboard by FIFO/write port.

## Useful Examples By Shape

Combinational sweep:
- `mux/sim/br_mux_bin_tb.sv`: parameterized inputs, `br_test_driver`, loop over `select`, `td.check_integer`.
- `shift/sim/br_shift_left_tb.sv`, `shift/sim/br_shift_right_tb.sv`, `shift/sim/br_shift_rotate_tb.sv`: build expected vectors in loops and compare each symbol.
- `enc/sim/br_enc_priority_dynamic_tb.sv`: local reference function for expected output.

Stateful directed scenarios:
- `counter/sim/br_counter_incr_tb.sv`, `counter/sim/br_counter_decr_tb.sv`, `counter/sim/br_counter_tb.sv`: reset, reinit, simple increment/decrement, boundary wrap/saturate checks.
- `multi_xfer/sim/br_multi_xfer_reg_fwd_tb.sv`: explicit scenarios for buffering, consuming, and pushing while popping.
- `lfsr/sim/br_lfsr_tb.sv`: model function plus period/balance checks.

Random with scoreboard:
- `ecc/sim/br_ecc_secded_encoder_decoder_tb.sv`: random data plus single/double-bit injection. Note the current zero-latency limitation before copying this style.
- `ram/sim/br_ram_flops_1r1w_tb.sv`: expected memory array scoreboard. Check local TODOs before using it as a latency model.
- `credit/sim/br_credit_sender_vc_rr_tb.sv`: per-VC queue scoreboard.

Ready/valid/FIFO:
- `fifo/sim/br_fifo_flops_tb.sv`: DUT plus `br_fifo_test_harness`, timeout, `error_count` check.
- `fifo/sim/br_fifo_flops_push_credit_tb.sv`: derives depth from modeled latency and credit behavior.
- `cdc/sim/br_cdc_fifo_flops_tb.sv`: CDC FIFO using same-clock smoke plus CDC delay plusargs.

Protocol/task-heavy:
- `csr/sim/br_csr_axil_widget_tb.sv`: AXI-Lite task drivers and CSR request/response checkers with timeouts.
- `csr/sim/br_csr_demux_tb.sv`: task-based request/response routing checks.
- `amba/sim/br_amba_axi_shrinker_tb.sv`: large task-oriented protocol test with transaction-specific checkers.
- `tracker/sim/br_tracker_freelist_tb.sv`: allocation/deallocation helpers, free-entry scoreboard, quiesce check.

## BUILD Skeleton

```bzl
load("@rules_hdl//verilog:providers.bzl", "verilog_library")
load("//bazel:br_verilog.bzl", "br_verilog_sim_test_tools_suite")
load("//bazel:verilog.bzl", "verilog_elab_test")

package(default_visibility = ["//visibility:private"])

verilog_library(
    name = "br_example_tb",
    srcs = ["br_example_tb.sv"],
    deps = [
        "//example/rtl:br_example",
        "//misc/sim:br_test_driver",
    ],
)

verilog_elab_test(
    name = "br_example_tb_elab_test",
    tool = "verific",
    deps = [":br_example_tb"],
)

br_verilog_sim_test_tools_suite(
    name = "br_example_sim_test_tools_suite",
    params = {
        "Width": ["1", "8", "17"],
    },
    tools = [
        "iverilog",
        "vcs",
        "verilator",
    ],
    deps = [":br_example_tb"],
)
```

If Verilator or Icarus cannot support the bench or dependent RTL, comment out only that tool and leave a short TODO with the reason.

`br_verilog_sim_test_tools_suite` also supplies the repository's standard simulation defines. Keep the wrapper for single-tool targets rather than replacing it with a raw `verilog_sim_test`. When only one tool needs an elaboration option, use a common suite for the unaffected tools and a separate narrowly scoped suite for that tool.

## Bench Boundaries And Naming

- Prefer one testbench file and one DUT instance for each distinct implementation policy. Fixed-priority, round-robin, and LRU variants should normally have separate benches even if their port lists match.
- A thin wrapper may use the underlying configurable module's bench as a base case when the wrapper adds no behavior and the parameterization remains obvious.
- Do not build a generic multi-DUT bench whose conditionals obscure the expected behavior. Small duplicated tasks are cheaper than a test harness that is difficult to review.
- The coverage inventory recognizes sim target names beginning with the DUT stem followed by `_tb`, `_gen_tb`, `_gen_unittest`, or `_sim_test_tools_suite`. Prefer those names. Add an entry to `COMPOSITE_DIRECT_BENCH_PREFIXES` only when sharing a bench is intentional.
- Repository lint treats `.svh` files as standalone inputs. Do not put module-scope declarations or tasks in a shared header unless the header is also valid when linted independently; use a package/helper module or keep the small helper local.

## Parameterization

- Use a testbench `parameter` only when the test derives its loops, stimulus, expected ordering, widths, and edge cases from that value.
- If directed behavior assumes exactly three requesters, two outputs, or another fixed shape, declare those values as `localparam` and do not expose a misleading Bazel override.
- Every Bazel parameter combination is a separate simulation target and typically recompiles in its own sandbox. Keep sweeps representative and make every point earn its compile cost.
- Do not duplicate DUT parameter legality checks in an `initial` block. RTL modules own them with `BR_ASSERT_STATIC`.

## Testbench Skeleton

```systemverilog
// SPDX-License-Identifier: Apache-2.0

module br_example_tb;

  parameter int Width = 8;
  parameter int NumItems = 16;

  logic clk;
  logic rst;

  logic push_valid;
  logic push_ready;
  logic [Width-1:0] push_data;
  logic pop_valid;
  logic pop_ready;
  logic [Width-1:0] pop_data;

  br_example #(
      .Width(Width)
  ) dut (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data,
      .pop_valid,
      .pop_ready,
      .pop_data
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic drive_item(input logic [Width-1:0] data);
    int timeout;
    timeout = 100;
    push_valid = 1'b1;
    push_data = data;
    while (!push_ready && timeout > 0) begin
      td.wait_cycles();
      timeout--;
    end
    td.check(timeout > 0, "Timed out waiting for push_ready");
    td.wait_cycles();
    push_valid = 1'b0;
    push_data = '0;
  endtask

  initial begin
    push_valid = 1'b0;
    push_data = '0;
    pop_ready = 1'b0;

    td.reset_dut();
    td.wait_cycles(2);

    pop_ready = 1'b1;
    for (int i = 0; i < NumItems; i++) begin
      drive_item(Width'(i));
    end

    td.wait_cycles(5);
    td.finish();
  end

endmodule : br_example_tb
```

Adapt the skeleton to the DUT rather than forcing every test through ready/valid tasks. For combinational DUTs, use a direct loop and compare against a local reference function instead.

## Tool Compatibility Checklist

VCS:
- Baseline target. Include it unless the test requires a tool-specific unsupported feature.

Verilator:
- Good for many simple/procedural benches.
- Avoid if dependent RTL enables internal assertions with unsupported multi-cycle SVA sequence constructs, especially delayed sequences using logical not.
- Avoid pass/fail requirements that depend on X detection or X propagation, such as `$isunknown(out)` for an invalid-select case.
- Existing exclusions appear in counter, FIFO, credit, CDC FIFO, AMBA, and some mux BUILD files.
- Diagnose warnings from the RTL before waiving them. For example, a packed matrix with disjoint continuously driven and registered bit regions may trigger Verilator's global `BLKANDNBLK` analysis even though the bits do not overlap. Document that exact cause and scope `-Wno-BLKANDNBLK` only to the affected suite.
- A local Verilator C++ compilation failure may be a host-toolchain problem rather than a repository problem. Verify the configured compiler and CI behavior before changing RTL or shared build rules.

Icarus:
- Good for simpler procedural benches.
- Avoid richer SystemVerilog/SVA-heavy benches, and cases already excluded nearby.
- Existing exclusions appear in priority encoder, some ECC, generated enc/ram, structured-gate mux, and one credit VC test.

## Coverage Expectations

Simulation tests should be useful smoke/regression tests, not formal replacements. Aim for:

- Reset and initial state.
- One or more normal transactions.
- Backpressure or stall behavior when applicable.
- Payload/data integrity on every accepted transfer.
- Contractual latency, cut-through behavior, and output stability while stalled.
- Every selectable route or requester at least once for routing/arbitration DUTs, plus simultaneous independent routes where the DUT promises parallel throughput.
- Policy-specific contention and state updates in a bench dedicated to that policy.
- Boundary values and parameter-sensitive behavior.
- A short random or permuted phase with a scoreboard for ordering/data integrity.
- Quiesce/drain at the end.

Leave exhaustive parameter sweeps, full protocol state-space coverage, and liveness/proof obligations to formal collateral.

## Validation Sequence

1. Run `pre-commit` on the changed bench and BUILD files, then `git diff --check`.
2. Run the bench's Verific elaboration target when present.
3. Run every generated VCS/Verilator/Icarus target for the changed bench with `--nocache_test_results`.
4. Run the containing area's simulation regression, for example `bazel test //flow/sim:all --test_tag_filters=sim --nocache_test_results`.
5. Run `python3 python/sim_tb_coverage_inventory.py` and confirm the intended DUTs are reported as direct benches.
6. Check `git status` after Bazel runs and discard unrelated generated lockfile churn before committing.
