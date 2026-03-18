# AGENTS.md

First, read the `README.adoc` file completely before proceeding.

## Verilog coding style

### Style guides

This repository follows the [xlsynth/verilog-style-guides](https://github.com/xlsynth/verilog-style-guides/).
Make sure that all Verilog code abides by the [general style guide](https://github.com/xlsynth/verilog-style-guides/blob/master/VerilogCodingStyle.md).

Simulation testbench code should additionally abide by the relevant parts of the [verification addendum](https://github.com/xlsynth/verilog-style-guides/blob/master/DVCodingStyle.md).
(This repository does not contain any UVM code, so ignore that part of the verification style guide.)

### Reuse existing code

When implementing RTL, always try to compose existing Bedrock libraries; don't write write a bespoke functional implementation unless it's genuinely new or if composition of existing modules will lead to suboptimal performance, power, or area.
RTL files will always be located beneath an `rtl/` subdirectory tree.

### Registers and sequential logic

This repository uses the following clock and reset conventions.
* Only use flip-flops; no latches.
* Flip-flops are triggered on the positive edge of the clock.
* Resets are synchronous and active-high.

Use the `BR_REG*` macros defined in `macros/br_registers.svh` for _all_ sequential logic; never write `always @(posedge clk)` or `always_ff` blocks.

### Assertions and Covers

Use the assertion and cover macros in `macros/br_asserts.svh` and `macros/br_asserts_internal.svh`.
Do not write `assert property`, etc. directly.

* Every RTL module should have `BR_ASSERT_STATIC` to check for legal parameter values.
* Checks on input constraints should be written with `*_INTG` macros, and placed at the top of the module body.
* Checks on output behavior (assuming that the input constraints are satisfied) must be written with `*_IMPL` macros, and preferably placed at the bottom of the module body, though sometimes it is acceptable to put them in the middle of the implementation if it helps readability.

## Building and testing

We use the Bazel build system.

To build targets, just run this:

```shell
bazel build //...
```

But to run most tests, you need a properly configured environment with access to relevant EDA tools, some of which are proprietary, as mentioned in the README.
To check if this is configured properly, read through `.bazelrc` and also check if there is a `user.bazelrc`.
If it looks like any of the required environment variables are not set or they're set to invalid paths, the environment may not be set up correctly.
You can smoke-test if the environment looks ready:

```shell
bazel run //:check_env
```

Assuming it's ok, you can run all tests:

```shell
bazel test //...
```

The above might take a long time, especially because proprietary EDA tools are typically license-limited and that can limit Bazel's test-level concurrency.
You can filter to run fewer tests using the typical Bazel path syntax.
We've also provided handy test tag filters by test type and by vendor tool.
For example:

```shell
bazel test //... --test_tag-filters=elab  # Run only elaboration tests
bazel test //... --test_tag-filters=verific  # Run only tests that use the `verific` tool
bazel test //... --test_tag-filters=sim  # Run only simulation tests, with all applicable tools
bazel test //... --test_tag-filters=vcs  # Run only tests that use the `vcs` tool (subset of all simulation tests)
```

Note that some Bazel tests do not require any EDA tools.
Notably:

```shell
bazel test //bazel/... //python/...
```

`pre-commit` will run code formatters.
