#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

tarball="$1"
runner="$2"
tar_contents="$(tar -tzf "$tarball")"

if [[ "$tar_contents" == *runner_env.sh* ]]; then
    echo "Sandbox tarball unexpectedly contains the environment hook" >&2
    exit 1
fi

if grep -q 'runner_env.sh' "$runner"; then
    echo "Final sandbox runner unexpectedly sources the environment hook" >&2
    exit 1
fi
