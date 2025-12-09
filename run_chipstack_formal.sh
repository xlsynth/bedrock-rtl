#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

# Launch ChipStack formal flow for a given Bazel target.
# Usage: ./run_chipstack_formal.sh --bazel-target //<pkg>/<path>:<label> --top <top_module_name> --flow <flow_name> [--run-id <id>] [--spec-file <path>] [--extra-instructions-file <path>] [--query <query>]

set -euo pipefail

# Simple flag parsing for required args.
BAZEL_TARGET=""
TOP_MODULE_NAME=""
FLOW_NAME=""
RUN_ID=""
SPEC_FILE=""
EXTRA_INSTRUCTIONS_FILE=""
QUERY_STR=""
print_usage() {
  echo "Usage: $0 --bazel-target //<pkg>/<path>:<label> --top <top_module_name> --flow <flow_name> [--run-id <id>] [--spec-file <path>] [--extra-instructions-file <path>] [--query <query>]" >&2
  echo "Available flows: launch-full-flow, generate-testplan, generate-testbench, update-testplan, update-testbench" >&2
  echo "Run ID: identifier used for the artifacts directory (required for all flows except launch-full-flow)" >&2
  echo "  Example: artifacts in ./chipstack_artifacts/br_counter-2025_11_24_21_03_26 => --run-id 2025_11_24_21_03_26" >&2
  echo "Spec file: optional spec file path passed through to ChipStack" >&2
  echo "Extra instructions file: optional instructions file path passed through to ChipStack" >&2
  echo "Query: optional query string; required for update-testplan and update-testbench" >&2
}
while [[ $# -gt 0 ]]; do
  case "$1" in
    --bazel-target)
      BAZEL_TARGET="$2"
      shift 2
      ;;
    --top)
      TOP_MODULE_NAME="$2"
      shift 2
      ;;
    --flow)
      FLOW_NAME="$2"
      shift 2
      ;;
    --run-id)
      RUN_ID="$2"
      shift 2
      ;;
    --spec-file)
      SPEC_FILE="$2"
      shift 2
      ;;
    --extra-instructions-file)
      EXTRA_INSTRUCTIONS_FILE="$2"
      shift 2
      ;;
    --query)
      QUERY_STR="$2"
      shift 2
      ;;
    -h|--help)
      print_usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      print_usage
      exit 1
      ;;
  esac
done

if [ -z "$BAZEL_TARGET" ] || [ -z "$TOP_MODULE_NAME" ] || [ -z "$FLOW_NAME" ]; then
  print_usage
  exit 1
fi

case "$FLOW_NAME" in
  launch-full-flow|generate-testplan|generate-testbench|update-testplan|update-testbench)
    ;;
  *)
    echo "Invalid flow: ${FLOW_NAME}" >&2
    print_usage
    exit 1
    ;;
esac

if [ "$FLOW_NAME" != "launch-full-flow" ] && [ -z "$RUN_ID" ]; then
  echo "--run-id is required for flow ${FLOW_NAME}" >&2
  print_usage
  exit 1
fi

if { [ "$FLOW_NAME" = "update-testplan" ] || [ "$FLOW_NAME" = "update-testbench" ]; } && [ -z "$QUERY_STR" ]; then
  echo "--query is required for flow ${FLOW_NAME}" >&2
  print_usage
  exit 1
fi

# Always run from the repo root so relative paths match generate_filelist.sh output.
REPO_ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$REPO_ROOT"

# TODO(xiyu-openai) change to MODULE file
CHIPSTACK_ROOT="/eda-tools/chipstack/chipstack_cli/0.64.1"
CHIPSTACK_BIN="${CHIPSTACK_ROOT}/chipstack"
CHIPSTACK_CONFIG="${CHIPSTACK_ROOT}/cli_config.yaml"

./generate_filelist.sh "$BAZEL_TARGET"

TARGET_SANITIZED="$(echo "$BAZEL_TARGET" | sed 's|//|_|g; s|/|_|g; s|:|_|g')"
FILELIST_PATH="filelist_paths_${TARGET_SANITIZED}.f"

if [ ! -f "$FILELIST_PATH" ]; then
  echo "Expected filelist not found at ${FILELIST_PATH}" >&2
  exit 1
fi

TARGET_NO_SLASH="${BAZEL_TARGET#//}"
TARGET_PACKAGE="${TARGET_NO_SLASH%%:*}"
TARGET_LABEL="${BAZEL_TARGET##*:}"
TOP_MODULE_FILE="./${TARGET_PACKAGE}/${TOP_MODULE_NAME}.sv"

# Require that the derived top module file is present in the generated filelist.
if ! grep -qx "$TOP_MODULE_FILE" "$FILELIST_PATH"; then
  echo "Derived top module file (${TOP_MODULE_FILE}) not found in ${FILELIST_PATH}" >&2
  echo "Check the Bazel target (${BAZEL_TARGET}) and top module name (${TOP_MODULE_NAME})." >&2
  exit 1
fi

echo "Using top module file: ${TOP_MODULE_FILE}"
echo "Running ChipStack formal flow..."

if [ -n "$RUN_ID" ]; then
  "$CHIPSTACK_BIN" \
    --config "$CHIPSTACK_CONFIG" \
    formal-agent "$FLOW_NAME" \
    --top-module-file "${TOP_MODULE_FILE}" \
    --filelist "${FILELIST_PATH}" \
    --top-module-name "${TOP_MODULE_NAME}" \
    --run-id "${RUN_ID}" \
    ${SPEC_FILE:+--spec-file "$SPEC_FILE"} \
    ${EXTRA_INSTRUCTIONS_FILE:+--extra-instructions-file "$EXTRA_INSTRUCTIONS_FILE"} \
    ${QUERY_STR:+--query "$QUERY_STR"}
else
  "$CHIPSTACK_BIN" \
    --config "$CHIPSTACK_CONFIG" \
    formal-agent "$FLOW_NAME" \
    --top-module-file "${TOP_MODULE_FILE}" \
    --filelist "${FILELIST_PATH}" \
    --top-module-name "${TOP_MODULE_NAME}" \
    ${SPEC_FILE:+--spec-file "$SPEC_FILE"} \
    ${EXTRA_INSTRUCTIONS_FILE:+--extra-instructions-file "$EXTRA_INSTRUCTIONS_FILE"} \
    ${QUERY_STR:+--query "$QUERY_STR"}
fi
