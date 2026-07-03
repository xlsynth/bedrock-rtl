---
name: write-br-testbench
description: Write or refactor Bedrock-RTL SystemVerilog simulation testbenches that use br_dv_lib class-based infrastructure. Use when Codex needs to create or update DUT-specific items, sequences, drivers, monitors, scoreboards, envs, br_dv_context/br_dv_env usage, br_dv_lib docs, or Bazel sim targets for a Bedrock RTL testbench.
---

# Write BR Testbench

Use this skill for Bedrock-RTL testbenches that should follow `br_dv_lib`
rather than older procedural helpers. Also use the repo's `write-sim-testbench`
skill when the task is mainly about simulator portability, Bazel target shape,
or existing non-`br_dv_lib` benches.

## First Reads

Before editing, inspect:

- `br_dv_lib/doc/user_guide.md` as the source of truth for current library API.
- The DUT RTL and closest analogous sim bench.
- The nearest `sim/BUILD.bazel`.
- The current `br_dv_lib/*.svh` classes if changing library infrastructure.

For compact br_dv_lib patterns from the RAM addr decoder work, read
`references/br-dv-lib-testbench-patterns.md`.

## Preferred Shape

Keep roles crisp:

- The top `*_tb.sv` module owns DUT/interfaces, test parameters, lifecycle, and
  scenario flow.
- `br_dv_context` owns checks, component registration, and shared orchestration
  helpers such as bounded sequence waits.
- A DUT-specific `br_dv_env` subclass owns topology only: object handles,
  `build()`, and `connect()`.
- Drivers are BFMs only. They drive protocol signals from items and put the
  interface idle on a `null` item.
- Monitors observe interfaces and publish captured items. They should not embed
  DUT prediction or protocol assertions that already belong to RTL assertions.
- Scoreboards own prediction, semantic port routing, matching, latency checks,
  and data-integrity checks.

Keep the monitor/scoreboard boundary simple: monitors publish only observed
valid transactions, and scoreboards consume those transactions. Do not make the
scoreboard resample live DUT interfaces to decide whether a monitor item was
valid.

## Implementation Workflow

1. Create a DUT-local package directory under `*/sim/<dut>_tb/`.
2. Put one class per `.svh` file: item, sequence, driver, monitor, scoreboard,
   and env when topology is nontrivial.
3. Add a local `BUILD.bazel` in that directory for the package, interface, TB,
   elaboration test, and sim suites. Keep outer `sim/BUILD.bazel` free of those
   DUT-local recipes.
4. Include class files from `<dut>_tb_pkg.sv`; import that package in the TB.
5. Instantiate DUT and virtual interfaces in `<dut>_tb.sv`.
6. Construct `ctx = new(test);`, then construct the DUT env with `ctx` and the
   interfaces.
7. Keep reset, sequence filling, iteration loops, drain cycles, and scoreboard
   checks in the TB scenario, not in the env.
8. Run the narrowest Bazel build/sim targets and `pre-commit run` on touched
   files.

When the DUT is parameterized, use the TB module parameters as the single source
of truth. Thread those parameters through interfaces, env, agents, monitors,
scoreboards, items, and Bazel suites. Avoid magic maximum widths in items; make
item payload fields parameterized by the DUT width, then verify with
elaboration and Verilator because parameterized class specializations can expose
tool issues.

For parameterized class benches, define DUT-specific item/env typedefs once near
the TB module parameters and pass those types through the env and agents. Avoid
repeating long class specializations in task signatures and scoreboard sinks.

## Coding Rules

- Use positive clock edges only in drivers and monitors.
- Use nonblocking assignments when driving DUT pins from BFMs.
- Never add `#1` or `@(negedge ...)` unless the user explicitly asks; if a
  temporary delay is required, leave a precise TODO explaining the tool issue.
- Do not bake traffic policy into drivers. Put policy in sequence constraints or
  `fill_*` helpers.
- Prefer one reusable sequence fill path with knobs or modes over several
  near-identical fill tasks. Add a separate helper only when sharing would make
  the base helper genuinely convoluted.
- After disabling or killing a sequence, explicitly drive the BFM idle before
  draining and checking the scoreboard.
- Prefer random constraints for item legality and traffic knobs instead of
  ad-hoc post-random mutation.
- Keep monitors passive: use `#1step` after the positive edge only for sampling
  values driven by NBAs, and never drive DUT inputs from monitors.
- Let monitors filter invalid and reset cycles before publishing items. If an
  item reaches the scoreboard, treat it as an observed transaction.
- Put monitor-assigned IDs, observed cycles, or timestamps into items whenever
  ordering, latency, or repeated payload values could otherwise hide bugs.
- When capturing or comparing parameterized packed data, keep both sides in the
  same DUT-width item type. Avoid `Width'(...)` casts for data values; for packed
  tile arrays, assign through a typed `logic [Width-1:0]` local if that is the
  clearest tool-portable conversion.
- Keep scoreboard inputs as semantic ports such as `write_in` and `write_out`.
  Use expected and actual queues with short names such as `exp_q` and `act_q`.
  Avoid callback-time assumptions; `write_*` methods may run after the sampled
  interface cycle, so base ordering and latency checks on item fields captured
  by monitors.
- Keep common runners generic. Scenario-specific helpers such as reset watchers
  should be forked in that scenario before calling the common runner, then
  disabled after it returns.
- Keep overrideable testbench parameters meaningful for coverage; derive helper
  widths, latencies, drain counts, and sequence timeouts with `localparam`.
  Include every directed and random sequence length in timeout sizing, especially
  user-overridable transaction-count parameters. Remove unused derived
  localparams unless they feed a check or implementation.
- Do not enable waves by default. Add plusarg-based VCD dumping only when useful
  and keep Bazel `waves = True` out of tests.
- Use plusarg-based VCD/FST dumping only when the local pattern supports it; do
  not leave unconditional dump blocks in the TB.

## Scenario and Coverage Guidance

For datapath or pipeline DUTs, include directed scenarios before random traffic:

- smoke: one valid transaction after reset,
- idle-data: drive payload data while valid is low,
- reset-during-valid: assert reset when valid traffic is actually observed,
- continuous stress: back-to-back valid transactions with no gaps,
- random batches: mixed valid and idle cycles.

For parameter sweeps, include edge cases around internal calculations:

- zero-stage combinational paths with real tiling,
- one dimension pipelined while the other is combinational,
- deeper latency with tiling active,
- odd and even tile counts,
- minimal widths such as `Width=1`,
- non-power-of-two widths that still satisfy DUT static constraints.

## Standard Scenario Skeleton

```systemverilog
task automatic run_sequence_and_check(input br_dv_context ctx, input my_env env);
  fork : sequence_run_fork
    env.input_sequence.start();
  join_none

  ctx.wait_for_sequences(env.clk_rst_driver, SequenceTimeoutCycles);
  disable sequence_run_fork;
  env.input_driver.drive_item(null);
  env.clk_rst_driver.wait_cycles(DrainCycles);
  env.scoreboard.check_all();
endtask

task automatic run_reset_test(input br_dv_context ctx, input my_env env);
  env.input_sequence.fill_random(ResetSequenceItems, ForceValidOrDirectedMode);
  fork : reset_on_valid_fork
    reset_on_next_valid(env);
  join_none
  run_sequence_and_check(ctx, env);
  disable reset_on_valid_fork;
endtask
```

Use `BR_DEFINE_TEST` and `BR_RUN_TEST` for test creation.

## Validation

Run validation proportional to the change:

1. Elaborate the TB.
2. Run one or more focused Verilator targets, especially any new or risky
   parameter sets. Include odd/non-power-of-two widths when data packing,
   casting, or item specialization changed.
3. Run the full affected Verilator suite when class specializations, monitors,
   scoreboards, reset flow, or Bazel suites changed.
4. Run touched-file `pre-commit`.

If Verilator fails, paste the relevant failure log in the chat before fixing it.

When reviewing a finished bench, check that scoreboards compare all relevant
semantic fields, latency expectations account for all parameter configurations,
reset helpers do not rely on simulator scheduling side effects, comments still
match behavior, and timeout/drain constants cover the largest generated
scenario.
