#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

#!/bin/bash
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
