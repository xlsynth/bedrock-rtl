#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

usage() {
  cat << EOF
Usage:
  bazel run //testplanner:generate_test_summary
  bazel run //testplanner:generate_test_summary -- <bazel_test_logs_path> <bazel_test_timestamp> <testlogs_path> <test_category> <output_path>

With no arguments, the script reads these environment variables:
  BAZEL_TEST_LOGS_PATH
  BAZEL_TEST_TIMESTAMP
  TESTLOGS_PATH
  TEST_CATEGORY
  OUTPUT_PATH
EOF
}

if [[ $# -eq 1 && ( "$1" == "-h" || "$1" == "--help" ) ]]; then
  usage
  exit 0
fi

if [[ $# -eq 0 ]]; then
  bazel_test_logs_path="${BAZEL_TEST_LOGS_PATH:-}"
  bazel_test_timestamp="${BAZEL_TEST_TIMESTAMP:-}"
  testlogs_path="${TESTLOGS_PATH:-}"
  test_category="${TEST_CATEGORY:-}"
  output_path="${OUTPUT_PATH:-}"
elif [[ $# -eq 5 ]]; then
  bazel_test_logs_path="$1"
  bazel_test_timestamp="$2"
  testlogs_path="$3"
  test_category="$4"
  output_path="$5"
else
  usage
  exit 1
fi

missing_args=()
[[ -n "${bazel_test_logs_path}" ]] || missing_args+=("BAZEL_TEST_LOGS_PATH")
[[ -n "${bazel_test_timestamp}" ]] || missing_args+=("BAZEL_TEST_TIMESTAMP")
[[ -n "${testlogs_path}" ]] || missing_args+=("TESTLOGS_PATH")
[[ -n "${test_category}" ]] || missing_args+=("TEST_CATEGORY")
[[ -n "${output_path}" ]] || missing_args+=("OUTPUT_PATH")

if [[ ${#missing_args[@]} -ne 0 ]]; then
  printf 'Missing required value(s): %s\n' "${missing_args[*]}"
  usage
  exit 1
fi

results_file="./.bazel-test-outputs.results"

if ! grep -E ' in [0-9]+' "${bazel_test_logs_path}" > "${results_file}"; then
  echo "No tests found in ${bazel_test_logs_path}"
  exit 1
fi

if ! python3 ./testplanner/generate_testplan.py "${results_file}" "${test_category}" "${output_path}/testplans"; then
  echo "generate_testplan.py failed"
  exit 1
fi

if ! python3 ./testplanner/generate_testreport.py "${results_file}" "${bazel_test_timestamp}" "${testlogs_path}" "${test_category}" "${output_path}/testreports"; then
  echo "generate_testreport.py failed"
  exit 1
fi
