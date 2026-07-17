#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

hooked_wrapper="$1"
unhooked_wrapper="$2"
quoted_hook_wrapper="$3"
hook_source="source 'bazel/verilog_env_test/runner_env.sh'"
quoted_hook_source="source 'bazel/verilog_env_test/runner_env'\"'\"'s.sh'"
plugin_export_prefix='export VERILOG_RUNNER_PLUGIN_PATH=${VERILOG_RUNNER_PLUGIN_PATH}:bazel/verilog_env_test/plugins:../'

unset_line="$(grep -nF 'unset -f rlocation' "$hooked_wrapper" | cut -d: -f1)"
hook_line="$(grep -nFx "$hook_source" "$hooked_wrapper" | cut -d: -f1)"
plugin_export_line="$(grep -nF "$plugin_export_prefix" "$hooked_wrapper" | cut -d: -f1)"
python_line="$(grep -n '^python3 .*fake_verilog_runner.py ' "$hooked_wrapper" | cut -d: -f1)"
test "$unset_line" -gt "$hook_line"
test "$plugin_export_line" -gt "$unset_line"
test "$python_line" -gt "$plugin_export_line"
grep -Fx "$quoted_hook_source" "$quoted_hook_wrapper"

if grep -q 'VERILOG_RUNNER_PLUGIN_PATH=.*:external/' "$hooked_wrapper"; then
    echo "Direct wrapper unexpectedly uses an execroot external plugin path" >&2
    exit 1
fi

if grep -q 'runner_env.sh' "$unhooked_wrapper"; then
    echo "Unconfigured wrapper unexpectedly references the environment hook" >&2
    exit 1
fi

unhooked_export_line="$(grep -n '^export VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP=' "$unhooked_wrapper" | cut -d: -f1)"
unhooked_unset_line="$(grep -nF 'unset -f rlocation' "$unhooked_wrapper" | cut -d: -f1)"
test "$unhooked_export_line" -lt "$unhooked_unset_line"
