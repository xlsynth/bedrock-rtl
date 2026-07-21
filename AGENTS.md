# AGENTS.md

Reading `README.md` in its entirety is not required, but it may provide helpful repository context. Before changing code, inspect the closest analogous module, test, and `BUILD.bazel` target and follow their established patterns.

## Repository layout

* Synthesizable design RTL belongs beneath a block's `rtl/` directory.
* Simulation testbenches and support code belong beneath `sim/`.
* Formal properties, monitors, and support code belong beneath `fpv/`.
* Bazel build files must be named `BUILD.bazel`, never `BUILD`.

## Verilog coding style

### Style guides

This repository follows the [xlsynth Verilog style guide](https://github.com/xlsynth/verilog-style-guides/blob/master/VerilogCodingStyle.md).

Simulation testbench code must also follow the relevant parts of the [verification addendum](https://github.com/xlsynth/verilog-style-guides/blob/master/DVCodingStyle.md). This repository does not use UVM, so its UVM-specific guidance does not apply.

### Reuse existing code

Prefer composing existing Bedrock modules over writing bespoke RTL. New implementations are appropriate when the functionality is genuinely new or composition would materially harm performance, power, or area.

### Registers and sequential logic

* Do not infer latches.
* Flip-flops are positive-edge triggered.
* Prefer synchronous, active-high resets. Use asynchronous resets only where the design requires them, such as CDC and reset-synchronization logic.
* For ordinary synthesizable flip-flop logic, use the appropriate `BR_REG*` macro from `macros/br_registers.svh` rather than writing an `always_ff` block directly.
* Direct sequential blocks may be appropriate for memories, verification code, or constructs that the register macros cannot express. Follow the closest existing implementation in those cases.

### Assertions and covers

Use the assertion and cover macros in `macros/br_asserts.svh`; do not write `assert property`, `cover property`, or similar constructs directly. Within Bedrock implementations, use the integration and implementation macros from `macros/br_asserts_internal.svh` where applicable.

* Parameterized RTL modules must use `BR_ASSERT_STATIC` to validate all nontrivial parameter constraints.
* Input and integration constraints should use `*_INTG` macros and appear near the top of the module body.
* Output behavior, assuming integration constraints are satisfied, should use `*_IMPL` macros. Prefer placing these checks near the bottom of the module unless keeping one near the relevant implementation improves readability.

## Bazel and verification

Use Bazel for builds and tests. Prefer validation proportional to the change:

1. Run the narrowest affected build and test targets first.
2. Expand to the relevant package, test type, or tool-filtered suite when appropriate.
3. Run repository-wide `//...` commands only when the scope or risk warrants them.

RTL behavior changes should generally add or update verification collateral. Use the appropriate combination of elaboration, lint, simulation, and formal tests; compilation alone is not sufficient evidence for a behavioral change.

Useful commands include:

```shell
bazel build //<affected/package>:<target>
bazel test //<affected/package>/...
bazel test //... --test_tag_filters=elab
bazel test //... --test_tag_filters=lint
bazel test //... --test_tag_filters=sim
bazel test //... --test_tag_filters=fpv
bazel test //... --test_tag_filters=<tool>
```

Many tests require locally configured EDA tools, including proprietary tools. Review `.bazelrc` and `user.bazelrc`, if present, and check the environment with:

```shell
bazel test //:check_env
```

Tests under `//bazel/...` and `//python/...` generally do not require EDA tools:

```shell
bazel test //bazel/... //python/...
```

Repository-wide commands can be expensive and license-limited:

```shell
bazel build //...
bazel test //...
```

Simulation targets must not enable waveform generation by default; `waves = True` is rejected by the repository checks.

## Formatting and repository checks

Run pre-commit before considering a change complete:

```shell
pre-commit run --all-files
```

Pre-commit may modify files. Review the resulting diff and rerun the checks until they pass. It performs more than formatting, including Verilog lint, secret scanning, filename checks, and repository-specific policy checks. For documentation-only changes, formatting and repository checks are generally sufficient; EDA tests are unnecessary unless the documentation affects executable examples or generated artifacts.

## Filing bugs

This repository provides a bug report form at
`.github/ISSUE_TEMPLATE/bug.yml`. Use this form when filing GitHub issues for
bugs instead of opening a blank issue. Include a clear symptom, select the kind
of bug, and provide exact instructions to reproduce it. Add the optional root
cause analysis, recommended fix, and first known bad commit when that
information is available.
