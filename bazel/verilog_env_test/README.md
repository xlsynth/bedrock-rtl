# Verilog Runner environment hook tests

This package verifies the optional `verilog_runner_env` hook without requiring
an EDA installation. The fixtures exercise the hook where Bedrock invokes
Verilog Runner and check that the hook does not leak into generated sandbox
artifacts.

| Path | Coverage |
| --- | --- |
| Direct elab, lint, sim, FPV, and synth wrappers | The hook is in runfiles and is sourced before Verilog Runner. Hook-provided and Bedrock-provided plugin paths are both retained, including an external-Bzlmod runfiles path. |
| FPV and synth sandbox generators | The hook is an action input and is sourced by its execroot path while generating the sandbox. |
| Final sandbox tarballs and runners | The hook is absent because these artifacts do not invoke Verilog Runner Python. |
| Rules without the attribute | Generated wrappers do not reference the hook and preserve the existing command ordering. |

The package also covers shell quoting with a generated hook whose filename
contains an apostrophe. `fake_verilog_runner.py` validates the resulting
environment and plugin-path composition when the wrappers and generators run.

Run the focused suite with:

```shell
bazel test //bazel/verilog_env_test:verilog_env_tests
```
