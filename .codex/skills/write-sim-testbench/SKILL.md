---
name: write-sim-testbench
description: Write or update one Bedrock-RTL SystemVerilog simulation testbench and its Bazel sim target. Use when Codex needs to add, refactor, debug, or review a verilog_sim_test/br_verilog_sim_test_tools_suite bench for VCS or Verilator, including parameterized tests, ready/valid stimulus, scoreboards, and portable smoke/regression coverage that complements formal verification.
---

# Write Sim Testbench

## Workflow

1. Read the repo instructions first: `README.adoc`, local `AGENTS.md` if present, the DUT RTL, the nearest `sim/BUILD.bazel`, and 1-3 similar benches in neighboring directories.
2. Choose a bench shape that matches the DUT:
   - Combinational datapath: exhaustive or directed procedural sweeps with a reference function.
   - Single-clock state/protocol: scenario tasks plus a small scoreboard and timeout.
   - Ready/valid or credit/valid: reuse `br_test_driver`, `br_test_rate_control`, `br_flow_test_driver`, `br_flow_test_sink`, FIFO harnesses, or an existing local harness before inventing a new driver.
   - Protocol-heavy modules: write task-based transactions and response checkers.
3. Decide DUT ownership before sharing code:
   - Use one bench per distinct DUT behavior or arbitration policy. Do not instantiate unrelated variants together merely to reduce duplication.
   - Reuse a bench for a thin wrapper only when the wrapper is genuinely a base parameterization of the same behavior and the resulting test remains clear.
   - Share small helpers only when they make each bench easier to read; accept modest duplication over preprocessor or generic-harness complexity.
4. Add a `*_tb.sv` module and a `BUILD.bazel` entry. Expose a testbench parameter only when changing it changes stimulus or expected coverage; otherwise make it a `localparam`. Sweep important parameters from Bazel using string values.
5. Keep VCS as the minimum simulator target; include Verilator when the bench and dependent RTL work with it.
6. Run formatting/lint, the narrowest relevant elaboration and simulation targets, the area simulation regression, and `python/sim_tb_coverage_inventory.py` when adding direct DUT coverage. If EDA tools are unavailable, at least verify labels/deps with `bazel query` or report that simulation could not be run.

Read `references/repo-patterns.md` when you need concrete examples, a BUILD skeleton, or simulator compatibility notes.

## Testbench Style

Use the existing Bedrock simulation utilities by default:

- Instantiate `br_test_driver td` for single-clock benches. Drive `logic clk, rst`; call `td.reset_dut()`, `td.wait_cycles()`, `td.check()`, `td.check_integer()`, and `td.finish()`.
- Use a no-port module named after the file, usually `br_<module>_tb`; instantiate the DUT as `dut` unless a local pattern does otherwise.
- Put genuinely swept knobs in `parameter` declarations and derive widths/latencies with `localparam`. If the stimulus or expected results assume a fixed value, use a `localparam` instead of advertising an override that the test does not cover.
- Prefer deterministic directed phases plus a bounded pseudo-random phase over a large random-only test. Include boundary cases: reset, idle, min/max sizes, full/empty or no-credit states, backpressure/stalls, bypass/cut-through paths, and drain/quiesce.
- Use existing random drivers for ordinary ready/valid traffic; write manual drivers only when a directed timing or protocol scenario needs precise control.
- Check data integrity for every accepted transfer, not only handshake/control behavior. Also check documented latency and output stability through stalls when applicable.
- Use scoreboards for ordering/data checks. Keep them simple: arrays for fixed-depth structures, queues for per-flow/per-VC expected data when supported by the selected tools.
- Add timeouts around every wait loop. Never rely on an unbounded `forever` or `while` in the main test flow without an external bounded completion check.
- Prefer `td.check*` and `$error` over SVA in simulation testbenches. Do not add `assert property` just to test behavior; internal RTL assertions and formal collateral carry the deeper proof load.
- Do not add `initial` parameter-validity checks to a bench. The DUT owns legal-parameter checks through `BR_ASSERT_STATIC`.

## Portability Rules

Target VCS first. Add Verilator when practical:

- Verilator often fails on dependent Bedrock internal SVA that uses multi-cycle sequence constructs, especially delayed sequence expressions with logical not. If those assertions are in the dependency closure, comment out `"verilator"` with a TODO explaining the unsupported construct.
- Before adding a Verilator warning waiver, identify the exact RTL construct that triggers it. Scope the waiver to the affected target and leave a comment describing the root cause; do not use a broad unexplained waiver.
- Treat local compiler/toolchain failures separately from RTL portability. Do not commit simulator or C++ standard fixes solely for a developer-machine issue when the repository CI image already works.
- Do not make a Verilator-enabled test depend on X-propagation semantics for pass/fail. Verilator is effectively 2-state in many practical cases; checks such as `$isunknown(out)` are usually not portable.
- For CDC simulations that use delay modeling, follow the existing plusarg/`SIMULATION` pattern and keep Verilator exclusions if the delay model uses unsupported process randomization.

## Bazel Integration

Use `verilog_library` for the bench, `verilog_elab_test(tool = "verific")` when appropriate, and `br_verilog_sim_test_tools_suite` for internal Bedrock sim suites.

- Add `//misc/sim:br_test_driver` when using `td`.
- Add helper deps explicitly: `//flow/sim:br_flow_test_driver`, `//flow/sim:br_flow_test_sink`, `//fifo/sim:br_fifo_test_harness`, mocks, packages, and macros as needed.
- Set `top = "..."` when the top cannot be inferred from a single dep or when extra mock deps are present.
- Use `params = {"Param": ["value0", "value1"]}` for sweeps. Keep sweeps representative, not exhaustive; formal handles broad coverage.
- Keep `br_verilog_sim_test_tools_suite` when its generated simulation defines are needed, even for a single tool. Split VCS and Verilator suites only when one tool needs scoped options or waivers.
- Name direct benches and generated sim targets with the DUT stem, normally `br_<dut>_tb` and `br_<dut>_sim_test_tools_suite`, so `python/sim_tb_coverage_inventory.py` recognizes them. Update the inventory's explicit composite aliases only for an intentional shared bench.
- Use `sim_opts` for plusargs and `tags = ["no-sandbox"]` only when the test needs preserved outputs or follows an existing local pattern.

## Before Finishing

Check these before finalizing a new or edited bench:

- The test has a clear pass/fail path and calls `td.finish()` or `$finish` after reporting errors.
- Every successful transaction checks payload/data integrity, and latency is checked when it is part of the DUT contract.
- Every wait-for-ready/valid loop has a timeout.
- Every externally overrideable parameter changes meaningful test coverage; fixed scenario dimensions are `localparam` values.
- The selected tool list matches the constructs used by the bench and dependent assertions.
- Every simulator waiver has a narrow scope and a comment naming the RTL root cause.
- The Bazel deps include the DUT, helper modules, mocks, packages, and macros needed by the testbench.
- The direct-bench target name is visible to `python/sim_tb_coverage_inventory.py`.
- New RTL-like helper modules follow repository reset/clock conventions and include static parameter checks where applicable.
