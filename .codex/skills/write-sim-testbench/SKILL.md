---
name: write-sim-testbench
description: Write or update one Bedrock-RTL SystemVerilog simulation testbench and its Bazel sim target. Use when Codex needs to add, refactor, debug, or review a verilog_sim_test/br_verilog_sim_test_tools_suite bench for VCS, Verilator, or Icarus, including parameterized tests, ready/valid stimulus, scoreboards, and portable smoke/regression coverage that complements formal verification.
---

# Write Sim Testbench

## Workflow

1. Read the repo instructions first: `README.adoc`, local `AGENTS.md` if present, the DUT RTL, the nearest `sim/BUILD.bazel`, and 1-3 similar benches in neighboring directories.
2. Choose a bench shape that matches the DUT:
   - Combinational datapath: exhaustive or directed procedural sweeps with a reference function.
   - Single-clock state/protocol: scenario tasks plus a small scoreboard and timeout.
   - Ready/valid or credit/valid: reuse `br_test_driver`, `br_test_rate_control`, `br_flow_test_driver`, `br_flow_test_sink`, FIFO harnesses, or an existing local harness before inventing a new driver.
   - Protocol-heavy modules: write task-based transactions and response checkers.
3. Add a parameterized `*_tb.sv` module and a `BUILD.bazel` entry. Keep VCS as the minimum simulator target; include Verilator and Icarus only when the bench and dependent RTL actually work with them.
4. Run the narrowest relevant Bazel target when the environment supports it. If EDA tools are unavailable, at least verify labels/deps with `bazel query` or report that simulation could not be run.

Read `references/repo-patterns.md` when you need concrete examples, a BUILD skeleton, or simulator compatibility notes.

## Testbench Style

Use the existing Bedrock simulation utilities by default:

- Instantiate `br_test_driver td` for single-clock benches. Drive `logic clk, rst`; call `td.reset_dut()`, `td.wait_cycles()`, `td.check()`, `td.check_integer()`, and `td.finish()`.
- Use a no-port module named after the file, usually `br_<module>_tb`; instantiate the DUT as `dut` unless a local pattern does otherwise.
- Put tunable knobs in `parameter` declarations and derive widths/latencies with `localparam`. Sweep important parameters from Bazel using string values.
- Prefer deterministic directed phases plus a bounded pseudo-random phase over a large random-only test. Include boundary cases: reset, idle, min/max sizes, full/empty or no-credit states, backpressure/stalls, bypass/cut-through paths, and drain/quiesce.
- Use scoreboards for ordering/data checks. Keep them simple: arrays for fixed-depth structures, queues for per-flow/per-VC expected data when supported by the selected tools.
- Add timeouts around every wait loop. Never rely on an unbounded `forever` or `while` in the main test flow without an external bounded completion check.
- Prefer `td.check*` and `$error` over SVA in simulation testbenches. Do not add `assert property` just to test behavior; internal RTL assertions and formal collateral carry the deeper proof load.

## Portability Rules

Target VCS first. Add Verilator and Icarus opportunistically:

- Verilator often fails on dependent Bedrock internal SVA that uses multi-cycle sequence constructs, especially delayed sequence expressions with logical not. If those assertions are in the dependency closure, comment out `"verilator"` with a TODO explaining the unsupported construct.
- Icarus has incomplete SystemVerilog/SVA support and may struggle with richer generated or protocol benches. If it fails for tool limitations, leave it out with a short BUILD comment.
- Do not make a Verilator-enabled test depend on X-propagation semantics for pass/fail. Verilator is effectively 2-state in many practical cases; checks such as `$isunknown(out)` are usually not portable.
- Avoid advanced testbench-only constructs unless existing nearby benches already use them with the same tool list: classes, clocking blocks, `process::self().srandom`, DPI, UVM, fork-heavy randomized environments, and complex SVA.
- For CDC simulations that use delay modeling, follow the existing plusarg/`SIMULATION` pattern and keep Verilator exclusions if the delay model uses unsupported process randomization.

## Bazel Integration

Use `verilog_library` for the bench, `verilog_elab_test(tool = "verific")` when appropriate, and `br_verilog_sim_test_tools_suite` for internal Bedrock sim suites.

- Add `//misc/sim:br_test_driver` when using `td`.
- Add helper deps explicitly: `//flow/sim:br_flow_test_driver`, `//flow/sim:br_flow_test_sink`, `//fifo/sim:br_fifo_test_harness`, mocks, packages, and macros as needed.
- Set `top = "..."` when the top cannot be inferred from a single dep or when extra mock deps are present.
- Use `params = {"Param": ["value0", "value1"]}` for sweeps. Keep sweeps representative, not exhaustive; formal handles broad coverage.
- Use `sim_opts` for plusargs and `tags = ["no-sandbox"]` only when the test needs preserved outputs or follows an existing local pattern.

## Before Finishing

Check these before finalizing a new or edited bench:

- The test has a clear pass/fail path and calls `td.finish()` or `$finish` after reporting errors.
- Every wait-for-ready/valid loop has a timeout.
- The selected tool list matches the constructs used by the bench and dependent assertions.
- The Bazel deps include the DUT, helper modules, mocks, packages, and macros needed by the testbench.
- New RTL-like helper modules follow repository reset/clock conventions and include static parameter checks where applicable.
