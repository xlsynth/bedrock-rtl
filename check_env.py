# SPDX-License-Identifier: Apache-2.0
#
# This script checks whether the local environment appears to be set up correctly for running tests.
# Run as `bazel test //:check_env`.

from shutil import which
import os
import subprocess
import sys

REQUIRED_ENV_VARS = [
    "VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP",
    "VERILOG_RUNNER_PLUGIN_PATH",
    "SLANG_PATH",
]

REQUIRED_BINARIES = [
    "ascentlint",
    "iverilog",
    "jg",
    "pre-commit",
    "vcf",
    "vcs",
    "verible-verilog-ls",
    "verible-verilog-lint",
    "verible-verilog-format",
    "xrun",
]

all_ok = True

print("Checking environment variables...", end="", flush=True)
ok = True
for var in REQUIRED_ENV_VARS:
    if not os.environ.get(var):
        if ok:
            print("FAIL")  # Go to a new line before printing first error
        ok = False
        print(f"--> {var} is not set")
if ok:
    print("Ok")
all_ok = all_ok and ok

print("Checking binaries exist...", end="", flush=True)
ok = True
for binary in REQUIRED_BINARIES:
    if which(binary) is None:
        if ok:
            print("FAIL")  # Go to a new line before printing first error
        ok = False
        print(f"--> Required binary '{binary}' is not found in PATH")
if ok:
    print("Ok")
all_ok = all_ok and ok

if not all_ok:
    sys.exit(1)
