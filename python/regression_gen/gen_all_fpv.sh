#!/bin/bash
set -euo pipefail

# Find the git root directory
GIT_ROOT=$(git rev-parse --show-toplevel)

# --- Pattern 1: <git root>/<block>/fpv ---
find "$GIT_ROOT" -mindepth 2 -maxdepth 2 -type d -name fpv | while read -r fpv_dir; do
    # Get the block name (parent directory of fpv)
    block=$(basename "$(dirname "$fpv_dir")")
    # Check that the directory is not under flow/fpv (to avoid overlap with pattern 2)
    rel_path="${fpv_dir#$GIT_ROOT/}"
    if [[ ! "$rel_path" =~ ^flow/fpv/ ]]; then
        echo "Generating for block: $block (directory: //$block/fpv)"
        bazel run //python/regression_gen:regression_gen -- --block "$block" --directory "//$block/fpv" --project "bedrock" --flow-name "jg_fpv" --description "Bedrock FPV regression." >/dev/null 2>&1
    fi
done

# --- Pattern 2: <git root>/flow/fpv/<block> ---
if [ -d "$GIT_ROOT/flow/fpv" ]; then
    find "$GIT_ROOT/flow/fpv" -mindepth 1 -maxdepth 1 -type d | while read -r block_dir; do
        block=$(basename "$block_dir")
        echo "Generating for flow block: flow_$block (directory: //flow/fpv/$block)"
        bazel run //python/regression_gen:regression_gen -- --block "flow_$block" --directory "//flow/fpv/$block" --project "bedrock" --flow-name "jg_fpv" --description "Bedrock flow regression." >/dev/null 2>&1
    done
fi
