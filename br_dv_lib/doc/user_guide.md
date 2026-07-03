# br_dv_lib User Guide

`br_dv_lib` is a lightweight SystemVerilog verification library for
Bedrock-RTL simulation tests. It provides a small class-based test harness,
typed items, drivers, sequences, monitors, scoreboards, environments, and sink
plumbing.

The library is intentionally not UVM. Testbenches should stay direct: instantiate
the DUT and interfaces in the testbench module, construct verification objects
inside `run_all_tests()`, connect them explicitly, run sequences, and check
scoreboards.

## Basic Test Structure

Every `br_dv_lib` testbench should:

- Import `br_dv_lib::*`.
- Include `br_dv_lib/br_dv_macros.svh`.
- Define `task automatic run_all_tests()` in the testbench module.
- Construct one `br_dv_context ctx = new(test);` inside `run_all_tests()`.
- Use `ctx.check(...)` and `ctx.check_integer(...)` for test checks.
- End with `BR_DEFINE_TEST` and `BR_RUN_TEST`.

```systemverilog
// SPDX-License-Identifier: Apache-2.0

module br_example_tb;
  import br_dv_lib::*;

  `include "br_dv_lib/br_dv_macros.svh"

  localparam time TestTimeout = 10us;

  br_dv_clk_rst_if clk_rst_if ();

  br_example dut (
      .clk(clk_rst_if.clk),
      .rst(clk_rst_if.rst)
  );

  task automatic run_all_tests();
    br_dv_context ctx;
    br_dv_clk_rst_driver clk_rst_driver;

    ctx = new(test);
    clk_rst_driver = new(ctx, clk_rst_if);

    clk_rst_driver.reset_dut();
    clk_rst_driver.wait_cycles();

    ctx.check(1'b1, "example check");
  endtask

  `BR_DEFINE_TEST(br_example_test, TestTimeout)
  `BR_RUN_TEST(br_example_test)
endmodule : br_example_tb
```

The `test` handle is created by `BR_RUN_TEST`. Use it only for test lifecycle
state, such as the timeout configured by `BR_DEFINE_TEST`. Use `ctx` for checks
and component orchestration.

## Test Lifecycle

`br_dv_test` owns the test lifecycle:

- Default timeout is `10000` time units.
- `set_timeout(timeout)` changes the timeout.
- `enable_vcd_dump(file_name)` enables `$dumpfile` / `$dumpvars`.
- `start()` starts optional VCD dumping and the timeout watchdog.
- `finish()` reports pass/fail based on the counted errors and calls `$finish`.
- `run()` is available for direct tests and calls `start()`, `test_body()`, and
  `finish()`.

Most testbenches should use the macros:

```systemverilog
`BR_DEFINE_TEST(br_example_test, TestTimeout)
`BR_RUN_TEST(br_example_test)
```

`BR_DEFINE_TEST` creates a small `br_dv_test` subclass whose `test_body()` calls
the module's `run_all_tests()` task. `BR_RUN_TEST` creates the test object, calls
`start()`, runs `run_all_tests()`, and then calls `finish()`.

## Context And Registration

`br_dv_context` is the shared object container for one test run:

```systemverilog
br_dv_context ctx;
ctx = new(test);
```

Pass `ctx` to component constructors. Components self-register through
`ctx.register(this)` and `get_kind()`. The context tracks:

- drivers
- monitors
- scoreboards
- sequences
- agents and environments

Do not manually push components into those lists. Construct the component with
`ctx`, and let the component register itself.

The context provides common checks:

```systemverilog
ctx.check(condition, "message");
ctx.check_integer(actual, expected, "message");
```

For sequence orchestration, `ctx.any_seq_has_item()` reports whether any
registered sequence still has queued items. `ctx.any_seq_is_running()` reports
whether any registered sequence is started or still has queued items.
`ctx.wait_for_sequences(clk_rst_driver, timeout_cycles)` waits for all
registered sequences to finish, advancing time with `clk_rst_driver.wait_cycles()`
and reporting a check failure on timeout.

## Clock And Reset Driver

`br_dv_clk_rst_driver` is a small helper for `br_dv_clk_rst_if`:

```systemverilog
br_dv_clk_rst_driver clk_rst_driver;
clk_rst_driver = new(ctx, clk_rst_if);
```

It provides:

- `wait_cycles(cycles = 1)`, which waits on positive clock edges.
- `reset_dut(reset_cycles = 1)`, which asserts synchronous active-high reset for
  the requested number of cycles.

## Items

All items derive from `br_item`.

```systemverilog
class my_item extends br_item;
  rand logic [31:0] data;

  function new(input logic [31:0] data = '0);
    super.new("my_item");
    this.data = data;
  endfunction
endclass
```

Put DUT-specific fields and intrinsic legality constraints on the item. Put
traffic-shaping policy in sequences.

## Drivers

A driver is the BFM. It is the only object that should drive protocol signals.
Generic drivers inherit from:

```systemverilog
class my_driver #(
    type ItemType = br_item
) extends br_dv_driver #(
    .ItemType(ItemType)
);
```

Override `drive_item(item)`:

```systemverilog
virtual task drive_item(input my_item item);
  if (item == null) begin
    drive_idle();
    return;
  end

  @(posedge clk_rst_vif.clk);
  vif.valid <= 1'b1;
  vif.data  <= item.data;
endtask
```

Sequences call the base driver's `drive_item_with_timeout(item)` wrapper. The
wrapper applies a watchdog around each `drive_item(item)` call.

Driver timeout API:

- `driver_timeout` defaults to `10000` time units.
- `set_driver_timeout(timeout)` configures it.
- Setting the timeout to `0` disables it.
- `poke_timeout()` restarts the watchdog for drivers that intentionally wait
  longer than one timeout interval.

`drive_item_with_timeout()` is base-class plumbing. Derived drivers should
override plain `drive_item()`.

## Sequences

A sequence produces items and feeds them to a connected typed driver. Generic
sequences inherit from:

```systemverilog
class my_sequence #(
    type ItemType = br_item
) extends br_dv_sequence #(
    .ItemType(ItemType)
);
```

The base sequence provides:

- `push_item(item)`
- `has_item()`
- `pop_item()`
- `connect(driver)`
- `is_connected()`
- `start()`
- `is_started()`
- `is_running()`

Create items in the sequence or test, push them into the sequence, connect the
sequence to a compatible typed driver, and call `start()`:

```systemverilog
sequence.connect(driver);
sequence.push_item(item);

fork
  sequence.start();
join_none
```

`start()` drives every queued item, pops each item after the driver accepts it,
and then sends one final `null` item through the driver. Drivers should treat the
`null` item as the end-of-sequence idle state.

For multiple sequences, use the context to wait until all registered sequences
are complete:

```systemverilog
fork
  addr_sequence.start();
  data_sequence.start();
join_none

ctx.wait_for_sequences(clk_rst_driver, SequenceTimeoutCycles);
```

The timeout value is test-owned. Pick a bound that reflects the expected traffic
and DUT latency.

## Monitors And Sinks

A monitor observes interfaces and publishes observed items to connected sinks.
Generic monitors inherit from:

```systemverilog
class my_monitor #(
    type ItemType = br_item
) extends br_dv_monitor #(
    .ItemType(ItemType)
);
```

Connect monitor output sinks explicitly:

```systemverilog
monitor.connect_sink(sink);
```

When the monitor observes a transaction, publish the item:

```systemverilog
publish(item);
```

A monitor can connect to any `br_dv_item_sink#(.ItemType(ItemType))`. This keeps
monitors independent of scoreboard internals. One monitor may also publish to
multiple sinks.

## Simple Scoreboards

For ordered expected-vs-actual comparisons, inherit from `br_dv_scoreboard`:

```systemverilog
class my_scoreboard extends br_dv_scoreboard #(
    .ItemType(my_item)
);
  function new(input br_dv_context ctx = null);
    super.new(ctx);
  endfunction

  virtual task compare_item(input my_item exp_item, input my_item act_item);
    ctx.check(exp_item.data === act_item.data, "data mismatch");
  endtask
endclass
```

`br_dv_scoreboard` owns two built-in sinks:

```systemverilog
input_monitor.connect_sink(scoreboard.get_exp_sink());
output_monitor.connect_sink(scoreboard.get_act_sink());
```

The built-in sink ports call `write_exp()` and `write_act()`, which enqueue
items. They do not compare immediately. Use `check_all()` when the test is ready
to compare all collected items:

```systemverilog
scoreboard.check_all();
```

Useful APIs:

- `get_exp_sink()`
- `get_act_sink()`
- `write_exp(item)`
- `write_act(item)`
- `get_pending_exp_items()`
- `get_pending_act_items()`
- `compare_all()`
- `check_empty()`
- `check_all()`

## Custom Scoreboard Ports

Some tests need more than two monitor inputs, semantic port names, or prediction
before enqueueing. In that case, inherit from `br_dv_port_sink_target` and create
typed `br_dv_port_sink` objects owned by the scoreboard.

```systemverilog
typedef enum {
  MySbIn,
  MySbOut
} my_scoreboard_port_e;

typedef br_dv_port_sink#(
    .ItemType(my_item),
    .PortType(my_scoreboard_port_e)
) my_scoreboard_sink_t;

class my_scoreboard extends br_dv_port_sink_target #(
    .ItemType(my_item),
    .PortType(my_scoreboard_port_e)
);
  local my_item exp_q[$];
  local my_item act_q[$];
  local my_scoreboard_sink_t in_sink;
  local my_scoreboard_sink_t out_sink;

  function new(input br_dv_context ctx = null);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
    in_sink  = new(this, MySbIn);
    out_sink = new(this, MySbOut);
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvScoreboard;
  endfunction

  function my_scoreboard_sink_t get_sink(input my_scoreboard_port_e port);
    case (port)
      MySbIn: return in_sink;
      MySbOut: return out_sink;
      default: return null;
    endcase
  endfunction

  task write_port(input my_scoreboard_port_e port, input my_item item);
    case (port)
      MySbIn: exp_q.push_back(predict(item));
      MySbOut: act_q.push_back(item);
      default: ctx.check(1'b0, "unknown scoreboard port");
    endcase
  endtask

  function my_item predict(input my_item item);
    return item;
  endfunction
endclass
```

Connect monitors to the named sinks:

```systemverilog
input_monitor.connect_sink(scoreboard.get_sink(MySbIn));
output_monitor.connect_sink(scoreboard.get_sink(MySbOut));
```

Use this pattern when the scoreboard needs explicit semantic ports. Use
`br_dv_scoreboard` when plain expected/actual queues are enough.

## Agents And Environments

`br_dv_agent` is a generic grouping component. It registers with the context as
an agent, but it does not assume a specific internal shape. Use it when a
protocol or test wants to group related objects, such as a driver, sequence, and
monitor.

The recommended pattern is:

- Keep `br_dv_agent` generic.
- Let protocol-specific agents construct and connect their children.
- Let child drivers, sequences, monitors, and scoreboards still self-register
  with the same context.

This keeps the context useful for debug and orchestration while still allowing
testbenches to hide repetitive protocol wiring behind an agent.

`br_dv_env` extends `br_dv_agent` and is the preferred base class for
testbench topology. It intentionally does not replace `br_dv_context`:

- The test owns lifecycle.
- The context owns services and component registration.
- The env owns the object graph and connections for one testbench.

Generic envs provide two overridable functions:

```systemverilog
virtual function void build();
endfunction

virtual function void connect();
endfunction
```

A DUT-specific env should own handles to drivers, sequences, monitors, and
scoreboards, then build and connect them in one place:

```systemverilog
class my_env extends br_dv_env;
  my_driver driver;
  my_sequence sequence;
  my_monitor input_monitor;
  my_monitor output_monitor;
  my_scoreboard scoreboard;

  function new(input br_dv_context ctx, /* virtual interfaces and params */);
    super.new(ctx);
    build();
    connect();
  endfunction

  virtual function void build();
    driver = new(ctx, /* interfaces */);
    sequence = new(ctx);
    input_monitor = new(ctx, /* interfaces */);
    output_monitor = new(ctx, /* interfaces */);
    scoreboard = new(ctx);
  endfunction

  virtual function void connect();
    sequence.connect(driver);
    input_monitor.connect_sink(scoreboard.get_exp_sink());
    output_monitor.connect_sink(scoreboard.get_act_sink());
  endfunction
endclass
```

Child components should still be constructed with `ctx` and self-register with
the context. The env only stores typed handles and centralizes wiring. Since
`br_dv_env` inherits from `br_dv_agent`, the env itself registers as an agent.

## Test-Local Classes

When a test needs custom items, drivers, sequences, monitors, or scoreboards,
put each class in its own `.svh` file and include those files from a test-local
package.

Recommended layout:

```text
ram/sim/br_example_tb/
  BUILD.bazel
  br_example_tb.sv
  br_example_tb_pkg.sv
  br_example_if.sv
  br_example_item.svh
  br_example_sequence.svh
  br_example_driver.svh
  br_example_monitor.svh
  br_example_scoreboard.svh
  br_example_env.svh
```

Package example:

```systemverilog
package br_example_tb_pkg;
  import br_dv_lib::*;

  `include "ram/sim/br_example_tb/br_example_item.svh"
  `include "ram/sim/br_example_tb/br_example_sequence.svh"
  `include "ram/sim/br_example_tb/br_example_driver.svh"
  `include "ram/sim/br_example_tb/br_example_monitor.svh"
  `include "ram/sim/br_example_tb/br_example_scoreboard.svh"
  `include "ram/sim/br_example_tb/br_example_env.svh"
endpackage : br_example_tb_pkg
```

The top testbench imports the package:

```systemverilog
module br_example_tb;
  import br_dv_lib::*;
  import br_example_tb_pkg::*;
```

This keeps compile order explicit and avoids putting multiple classes directly
inside the testbench module.

## BUILD.bazel Integration

For a testbench with test-local classes, prefer a local `BUILD.bazel` in the
testbench directory:

```bzl
verilog_library(
    name = "br_example_tb_pkg",
    srcs = ["br_example_tb_pkg.sv"],
    hdrs = [
        "br_example_driver.svh",
        "br_example_env.svh",
        "br_example_item.svh",
        "br_example_monitor.svh",
        "br_example_scoreboard.svh",
        "br_example_sequence.svh",
    ],
    deps = [
        "//br_dv_lib:br_dv_test",
    ],
)

verilog_library(
    name = "br_example_tb",
    srcs = ["br_example_tb.sv"],
    deps = [
        ":br_example_tb_pkg",
        "//br_dv_lib:br_dv_test",
        "//example/rtl:br_example",
    ],
)
```

Add an elaboration or simulation target following the nearest existing
`sim/BUILD.bazel` pattern.

## Recommended Test Flow

A typical class-based test should follow this order:

1. Construct `ctx`.
2. Construct a DUT-specific env.
3. Let the env construct clock/reset helpers, protocol drivers, sequences,
   monitors, and scoreboards.
4. Let the env connect sequences, drivers, monitors, and scoreboard sinks.
5. Let the testbench scenario fill sequences with directed or random items.
6. Let the testbench scenario reset the DUT, start sequences, wait with bounded
   timeouts, drain the DUT if needed, and run scoreboard checks.

Example:

```systemverilog
ctx = new(test);

env = new(ctx, clk_rst_if, input_if, output_if);

env.clk_rst_driver.reset_dut();

env.input_sequence.fill_random(100);

fork
  env.input_sequence.start();
join_none

ctx.wait_for_sequences(env.clk_rst_driver, SequenceTimeoutCycles);

env.scoreboard.check_all();
```

## Best Practices

- Keep the testbench module thin. Put reusable behavior in classes.
- Keep one class per `.svh` file.
- Put generic classes in `br_dv_lib/`.
- Put reusable protocol-specific classes in protocol packages.
- Put DUT-specific classes in a test-local package.
- Put DUT-specific topology and connection code in a `br_dv_env` subclass.
- Let components self-register by passing `ctx` to constructors.
- Keep drivers responsible for signal driving and protocol wait behavior.
- Keep sequences responsible for producing and queuing item data.
- Keep monitors responsible for observing interfaces and publishing items.
- Keep scoreboards responsible for prediction and data-integrity checks.
- Prefer named custom scoreboard ports when expected/actual does not describe
  the test clearly.
- Use `ctx.check` and `ctx.check_integer` instead of direct `$error` in normal
  test checks.
- Use `BR_DEFINE_TEST` and `BR_RUN_TEST`; do not hand-write the initial test
  construction block.
- Run the narrowest useful Bazel build and simulation target after changes.

## Verilator Note

If a Verilator run fails with an internal error or `Error-Unsupported`, stop and
identify the source line that triggered the tool failure before attempting a
workaround. Treat ordinary syntax, type, or test failures as normal bugs to fix.
