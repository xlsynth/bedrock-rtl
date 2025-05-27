#!/bin/bash
set -euo pipefail

# Find the git root directory
GIT_ROOT=$(git rev-parse --show-toplevel)

bazel build //python/regression_gen:regression_gen >/dev/null 2>&1
BIN_PATH=$(bazel info bazel-bin)/python/regression_gen/regression_gen

# --- Pattern 1: <git root>/<block>/fpv ---
yaml_paths_file=$(mktemp)
trap 'rm -f "$yaml_paths_file"' EXIT

find "$GIT_ROOT" -mindepth 2 -maxdepth 2 -type d -name fpv | while read -r fpv_dir; do
    # Get the block name (parent directory of fpv)
    block=$(basename "$(dirname "$fpv_dir")")
    # Check that the directory is not under flow/fpv (to avoid overlap with pattern 2)
    rel_path="${fpv_dir#$GIT_ROOT/}"
    if [[ ! "$rel_path" =~ ^flow/fpv/ ]]; then
        # echo "Generating for block: $block (directory: //$block/fpv)"
        "$BIN_PATH" --block "$block" --directory "//$block/fpv" --project "bedrock" --flow-name "jg_fpv" --description "Bedrock FPV regression." --output regr.yaml
        # Find all .yaml files generated in this fpv directory
        for yaml_file in "$fpv_dir"/regr.yaml; do
            [ -e "$yaml_file" ] && echo "$yaml_file" >> "$yaml_paths_file"
        done
    fi
done

# --- Pattern 2: <git root>/flow/fpv/<block> ---
if [ -d "$GIT_ROOT/flow/fpv" ]; then
    find "$GIT_ROOT/flow/fpv" -mindepth 1 -maxdepth 1 -type d | while read -r block_dir; do
        block=$(basename "$block_dir")
        # echo "Generating for flow-controlled block: flow_$block (directory: //flow/fpv/$block)"
        "$BIN_PATH" --block "flow_$block" --directory "//flow/fpv/$block" --project "bedrock" --flow-name "jg_fpv" --description "Bedrock flow regression." --output regr.yaml
        # Find all .yaml files generated in this flow/fpv block directory
        for yaml_file in "$block_dir"/regr.yaml; do
            [ -e "$yaml_file" ] && echo "$yaml_file" >> "$yaml_paths_file"
        done
    done
fi

# --- Generate all.yaml importing all found yamls ---
ALL_YAML_DIR="$GIT_ROOT/fpv/regression"
ALL_YAML_FILE="$ALL_YAML_DIR/all.yaml"
mkdir -p "$ALL_YAML_DIR"

# Remove duplicates and sort
mapfile -t unique_yaml_paths < <(sort -u "$yaml_paths_file")

{
    echo "import_yaml:"
    for yaml_abs in "${unique_yaml_paths[@]}"; do
        # Compute the relative path from $ALL_YAML_DIR to $yaml_abs
        rel_path=$(realpath --relative-to="$ALL_YAML_DIR" "$yaml_abs")
        echo "- $rel_path"
    done
} > "$ALL_YAML_FILE"

echo "Generated $ALL_YAML_FILE with imports to all found regression yamls."
