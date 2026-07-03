# br_dv_lib Testbench Patterns

Use this reference when implementing or refactoring a class-based Bedrock
testbench with `br_dv_lib`. Prefer `br_dv_lib/doc/user_guide.md` when it is
available; this file captures the design decisions from the RAM addr decoder
testbench discussion.

## Class Split

Use a self-contained simulation package directory:

```text
<block>/sim/<dut>_tb/
  BUILD.bazel
  <dut>_if.sv
  <dut>_tb.sv
  <dut>_tb_pkg.sv
  <dut>_item.svh
  <dut>_sequence.svh
  <dut>_driver.svh
  <dut>_monitor.svh
  <dut>_scoreboard.svh
  <dut>_env.svh
```

Prefer moving DUT-local Bazel recipes into this directory instead of growing a
large outer `sim/BUILD.bazel`. Keep source paths local inside the package's
`BUILD.bazel`, and keep SystemVerilog include paths repo-root-relative.

- `*_item.svh`: carry transaction fields. Add comments next to non-obvious
  fields such as IDs, timestamps, valid flags, or tile indexes.
- `*_sequence.svh`: produce and queue randomized or directed items. Use
  `rand`, `constraint`, and item legality constraints where practical.
- `*_driver.svh`: drive DUT input pins. For no-backpressure valid-only BFMs,
  drive item fields and valid on `@(posedge clk_rst_vif.clk)` with NBAs. On a
  `null` item, drive idle.
- `*_monitor.svh`: sample interface pins, build captured items, and `publish`.
  Avoid prediction and avoid duplicating DUT assertions.
- `*_scoreboard.svh`: own sink ports, prediction functions, expected/actual
  matching, alias/ID checks, and latency checks.
- `*_env.svh`: extend `br_dv_env`; store typed handles and implement
  `build()`/`connect()` only.

## Context, Test, And Env

Keep the split stable:

- `br_dv_test`: lifecycle, global timeout, VCD setup, final pass/fail.
- `br_dv_context`: registration, checks, sequence state, shared wait helpers.
- `br_dv_env`: topology and connections.
- TB module: scenario control, reset timing, random iteration count, drain
  cycles, and final scoreboard checks.

Do not move reset, iterations, or scoreboard checks into the env just to shrink
the TB. That makes the env a hidden test.

## Driver Pattern

For a simple valid-only BFM with no backpressure:

```systemverilog
virtual task drive_item(input my_item item);
  if (item == null) begin
    @(posedge clk_rst_vif.clk);
    drive_idle();
    return;
  end

  @(posedge clk_rst_vif.clk);
  vif.valid <= item.has_payload;
  vif.data  <= Width'(item.data);
endtask
```

Notes:

- Use `clk_rst_vif.clk` for timing.
- Use NBAs when driving interface signals.
- Put all driven signals into a known idle state in the constructor and on a
  `null` item.
- Do not force an explicit valid-low cycle after every item; the sequence sends
  `null` at end-of-sequence and the driver idle path handles quiescence.
- Do not add idle-cycle parameters to the driver unless they are part of the
  protocol. Traffic gaps belong in sequences.

## Monitor And Scoreboard Pattern

Prefer monitors that are reusable over scalar/tiled variants when the interface
shape differs only by a `Tiles` parameter. Let the monitor capture tile data and
valid bits literally, then let the scoreboard decide what those observations
mean.

Scoreboards should expose named sinks when expected/actual is not expressive
enough:

```systemverilog
input_monitor.connect_sink(scoreboard.get_sink(MySbIn));
output_monitor.connect_sink(scoreboard.get_sink(MySbOut));
```

Use explicit prediction functions:

```systemverilog
function my_item predict(input my_item actual);
  my_item predicted;
  predicted = actual.copy();
  // Transform input-side observation into expected output-side observation.
  return predicted;
endfunction
```

Track IDs or timestamps in items when value aliasing, ordering ambiguity, or
latency coverage could hide bugs.

For fixed-latency datapaths, have monitors stamp each observed transaction with
a monotonically increasing ID and observed cycle. Let the scoreboard check ID,
data, exact latency, and empty expected/actual queues. This catches repeated
payload aliases and off-by-one pipeline errors that pure data comparison can
miss.

When an input interface has semantic ports, such as depth tiles or lanes, keep
the driver responsible for legal pin-level encoding and the monitor responsible
for publishing one item per observed semantic transaction. Leave illegal
integration traffic to RTL assertions or FPV unless the test is explicitly
negative.

## Randomization

Use simple constraints for 50/50 booleans:

```systemverilog
void'(item.randomize() with {
  addr <= MaxAddressValue;
  allow_data -> has_data;
  !allow_data -> !has_data;
});
```

A plain unconstrained `rand bit has_addr;` is already 50/50; avoid noisy
`dist {0 := 1, 1 := 1}` unless the weighting is intentionally nonuniform.

Use sequence fill helpers for directed traffic modes instead of adding policy
to the driver. For example, a valid-only datapath can use an enum for random,
forced idle, and forced active traffic while sharing one item creation path.

## Parameter Sweeps

Keep Bazel suites representative and named by purpose. For pipelined tiled
datapaths, prefer separate suites for:

- zero and nonzero latency stages,
- tile fan-in/fan-out behavior,
- edge combinations where one dimension has zero stages,
- a deeper latency case,
- minimum data width,
- odd or non-power-of-two legal shapes.

## Validation

After edits:

- `bazel build //<pkg>:<tb_target>`
- Run one or more representative generated sim tests, usually Verilator plus
  VCS where available.
- Run `pre-commit run --files ...` on touched files.

When adding a broad parameter sweep, first run representative cases. For VCD
reruns, use plusargs or existing local conventions; do not enable waves by
default in Bazel.
