# SPDX-License-Identifier: Apache-2.0

import os
import pathlib
import sys


def _argument_value(prefix):
    for argument in sys.argv[1:]:
        if argument.startswith(prefix):
            return argument[len(prefix) :]
    return None


without_env = any("without_env" in argument for argument in sys.argv)
generator = "--dry-run" in sys.argv
if not without_env:
    if os.environ.get("VERILOG_RUNNER_ENV_TEST_LOADED") != "1":
        raise RuntimeError("Verilog Runner environment hook was not sourced")

plugin_paths = os.environ.get("VERILOG_RUNNER_PLUGIN_PATH", "").split(":")
expected_external_prefix = "external/" if generator else "../"
expected_plugin_paths = [
    "bazel/verilog_env_test/plugins",
    next(
        path
        for path in plugin_paths
        if path.startswith(expected_external_prefix) and path.endswith("/verilog")
    ),
]
if not all(path in plugin_paths for path in expected_plugin_paths):
    raise RuntimeError("Bedrock Verilog Runner plugin path was not appended")
if not without_env:
    expected_plugin_paths.insert(0, "/hook/verilog_runner_plugins")
    if plugin_paths != expected_plugin_paths:
        raise RuntimeError(
            "environment hook Verilog Runner plugin path was not preserved"
        )

for prefix in ("--filelist=", "--tcl="):
    output = _argument_value(prefix)
    if output:
        pathlib.Path(output).write_text("", encoding="utf-8")

script = _argument_value("--script=")
if script:
    pathlib.Path(script).write_text("#!/usr/bin/env bash\ntrue\n", encoding="utf-8")
