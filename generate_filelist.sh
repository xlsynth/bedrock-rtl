#!/bin/bash

# Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# ===============================================
# Script to generate a list of source files (.sv and .svh)
# Usage:
#   ./generate_filelist.sh <target> [output_path]
#
# Arguments:
#   <target>       : Bazel target for which to generate the file list (required).
#   [output_path]  : (Optional) Directory where the output file will be saved.
#                    If not provided, the file will be saved in the current directory.
#
# Output:
#   Generates a filelist with the name `filelist_paths_<sanitized_target>.f`
#   containing a list of paths to the source files (.sv and .svh) related to the given target.
#   The file starts with `+incdir+./macros` and includes `./` for each file.
#
# Examples:
#   1. Default behavior (current directory):
#      ./generate_filelist.sh //arb/rtl:br_arb_fixed_elab_test
#      Output file: ./filelist_paths_arb_rtl_br_arb_fixed_elab_test.f
#
#   2. Custom output path:
#      ./generate_filelist.sh //arb/rtl:br_arb_fixed_elab_test /path/to/output
#      Output file: /path/to/output/filelist_paths_arb_rtl_br_arb_fixed_elab_test.f
# ===============================================

# Check if target argument is provided
if [ -z "$1" ]; then
  echo "Usage: $0 <target> [output_path]"
  exit 1
fi

# Assign the target passed as an argument
TARGET=$1

# Sanitize the target name by replacing `//` and `/` with `_` and handling `:` similarly
TARGET_SANITIZED=$(echo "$TARGET" | sed 's|//|_|g; s|/|_|g; s|:|_|g')

# If output path is provided, use it, otherwise default to current directory
if [ -n "$2" ]; then
  OUTPUT_PATH="$2"
  # Ensure the output path exists
  mkdir -p "$OUTPUT_PATH"
else
  OUTPUT_PATH="."
fi

# Define the output file with the sanitized target name and .f extension in the specified path
PATHS_OUTPUT_FILE="${OUTPUT_PATH}/filelist_paths_${TARGET_SANITIZED}.f"

# Add `+incdir+./macros` at the top of the file
echo "+incdir+./macros" > "$PATHS_OUTPUT_FILE"

# Run the bazel query command, filter for .sv and .svh files, format the paths, and append `./` to each line
bazel query "kind('source file', deps(${TARGET}))" --output=label | grep -E "\\.sv$|\\.svh$" | sed 's|//|/|g; s|:|/|g; s|^|.|' >> "$PATHS_OUTPUT_FILE"

# Notify the user
echo "File list generated and saved to ${PATHS_OUTPUT_FILE}"
