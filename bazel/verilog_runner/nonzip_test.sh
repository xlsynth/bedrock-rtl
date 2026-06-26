#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

repo="${TEST_SRCDIR}/${TEST_WORKSPACE}"

if grep -q "verilog_runner_zipapp" "${repo}/bazel/verilog.bzl"; then
  echo "bazel/verilog.bzl still references verilog_runner_zipapp"
  exit 1
fi

for kind in elab lint sim fpv synth; do
  wrapper="${repo}/bazel/verilog_runner/nonzip_${kind}_test_runner.sh"
  if [[ ! -f "${wrapper}" ]]; then
    echo "missing generated wrapper: ${wrapper}"
    exit 1
  fi
  if ! grep -q "python3 python/verilog_runner/verilog_runner.py" "${wrapper}"; then
    echo "generated wrapper does not invoke the source runner through python3: ${wrapper}"
    exit 1
  fi
  if grep -q "python/verilog_runner/verilog_runner " "${wrapper}"; then
    echo "generated wrapper invokes the py_binary runner: ${wrapper}"
    exit 1
  fi
  if grep -q "verilog_runner_zipapp" "${wrapper}"; then
    echo "generated wrapper still references verilog_runner_zipapp: ${wrapper}"
    exit 1
  fi
done

synth_sandbox="${repo}/bazel/verilog_runner/nonzip_synth_sandbox.tar.gz"
synth_sandbox_runner="${repo}/bazel/verilog_runner/nonzip_synth_sandbox_runner.sh"
for output in "${synth_sandbox}" "${synth_sandbox_runner}"; do
  if [[ ! -f "${output}" ]]; then
    echo "missing generated synthesis sandbox output: ${output}"
    exit 1
  fi
done

archive_contents="$(tar -tzf "${synth_sandbox}")"
for required in \
  bazel/verilog_runner/nonzip_smoke.sv \
  python/verilog_runner/verilog_runner.py \
  python/verilog_runner/plugins/yosys.py \
  nonzip_synth_sandbox.f \
  nonzip_synth_sandbox.tcl \
  nonzip_synth_sandbox.sh; do
  if ! grep -Fxq "${required}" <<< "${archive_contents}"; then
    echo "synthesis sandbox is missing ${required}"
    exit 1
  fi
done

if grep -Eq '/yosys$' <<< "${archive_contents}"; then
  echo "synthesis sandbox unexpectedly bundles the Yosys executable"
  exit 1
fi

for file in \
  python/verilog_runner/verilog_runner.py \
  python/verilog_runner/cli.py \
  python/verilog_runner/eda_tool.py \
  python/verilog_runner/plugins.py \
  python/verilog_runner/util.py \
  python/verilog_runner/plugins/slang.py \
  python/verilog_runner/plugins/verilator.py \
  python/verilog_runner/plugins/yosys.py; do
  if [[ ! -f "${repo}/${file}" ]]; then
    echo "missing Verilog runner runfile: ${file}"
    exit 1
  fi
done

if find "${TEST_SRCDIR}" -maxdepth 4 -type d -name 'rules_python~~python*' | grep -q .; then
  echo "Verilog test runfiles include the rules_python interpreter runtime"
  exit 1
fi
