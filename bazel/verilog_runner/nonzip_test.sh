#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

repo="${TEST_SRCDIR}/${TEST_WORKSPACE}"

if grep -q "verilog_runner_zipapp" "${repo}/bazel/verilog.bzl"; then
  echo "bazel/verilog.bzl still references verilog_runner_zipapp"
  exit 1
fi

for kind in elab lint sim fpv; do
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

for file in \
  python/verilog_runner/verilog_runner.py \
  python/verilog_runner/cli.py \
  python/verilog_runner/eda_tool.py \
  python/verilog_runner/plugins.py \
  python/verilog_runner/util.py \
  python/verilog_runner/plugins/iverilog.py \
  python/verilog_runner/plugins/verilator.py; do
  if [[ ! -f "${repo}/${file}" ]]; then
    echo "missing Verilog runner runfile: ${file}"
    exit 1
  fi
done

if find "${TEST_SRCDIR}" -maxdepth 4 -type d -name 'rules_python~~python*' | grep -q .; then
  echo "Verilog test runfiles include the rules_python interpreter runtime"
  exit 1
fi
