#!/usr/bin/env python3
r"""This script generates per-day yamls in fpv/regression/generated/ and
per-block yamls in fpv/regression/generated/<day>/.

Usage:
    python gen_all.py

It uses the following configuration:
- DAY_BLOCK_MAP: Map block name regex patterns to days and attributes.
- DAYS: List of days.
- BLOCK_TIMEOUTS: Map block name patterns to timeouts (seconds).
- Other attributes can be added here as needed.

It uses the regression_gen tool to generate the yamls.
"""

from collections import defaultdict
from enum import Enum
import os
from pathlib import Path
import re
import subprocess
import sys


# --- Configuration ---
class Day(Enum):
    MON = 1
    TUE = 2
    WED = 3
    THU = 4
    FRI = 5
    SAT = 6
    SUN = 7


# Map block name regex patterns to days and attributes
DAY_BLOCK_MAP = {
    Day.MON: [r"^amba$", r"^arb$"],
    Day.TUE: [r"^cdc$"],
    Day.WED: [r"^ecc$", r"^counter$", r"^credit$", r"^delay$"],
    Day.THU: [r"^flow_.*$"],
    Day.FRI: [r"^fifo$"],
    Day.SAT: [r"^ram$"],
    # 'sun' is for unmatched
}
DAYS = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI, Day.SAT, Day.SUN]


# --- Helper Functions ---
def get_git_root():
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], encoding="utf-8"
        )
        return out.strip()
    except Exception as e:
        print("Error: Not in a git repository or git not found.", file=sys.stderr)
        sys.exit(1)


def run_bazel_build():
    try:
        subprocess.check_call(
            ["bazel", "build", "//python/regression_gen:regression_gen"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception as e:
        print("Error: Bazel build failed:", e, file=sys.stderr)
        sys.exit(1)


def get_bazel_bin_path():
    try:
        out = subprocess.check_output(["bazel", "info", "bazel-bin"], encoding="utf-8")
        return out.strip()
    except Exception as e:
        print("Error: Could not get bazel-bin path.", file=sys.stderr)
        sys.exit(1)


def match_day(block):
    block_lower = block.lower()
    for day, patterns in DAY_BLOCK_MAP.items():
        for pat in patterns:
            if re.fullmatch(pat, block_lower):
                return day
    return Day.SUN


def ensure_dir(path):
    os.makedirs(path, exist_ok=True)


def relative_path(from_dir, to_path):
    return os.path.relpath(to_path, from_dir)


def write_yaml_imports(yaml_path, rel_yaml_paths):
    with open(yaml_path, "w") as f:
        f.write("import_yaml:\n")
        for rel_path in sorted(rel_yaml_paths):
            f.write(f"- {rel_path}\n")


# --- Main Logic ---


def main():
    git_root = get_git_root()
    os.chdir(git_root)

    run_bazel_build()
    bazel_bin = get_bazel_bin_path()
    bin_path = os.path.join(bazel_bin, "python/regression_gen/regression_gen")

    generated_dir = os.path.join("fpv", "regression", "generated")
    ensure_dir(generated_dir)

    # Prepare per-day directories
    day_dirs = {day: os.path.join(generated_dir, f"Day{day.value}") for day in DAYS}
    for d in day_dirs.values():
        ensure_dir(d)

    # Collect all block info: {day: [(block, block_dir, is_flow)]}
    day_blocks = defaultdict(list)
    block_yaml_paths = defaultdict(list)  # {day: [yaml_path, ...]}

    # --- Pattern 1: <git root>/<block>/fpv ---
    for root, dirs, files in os.walk(git_root):
        # Only look for directories named 'fpv' at depth 2
        rel_root = os.path.relpath(root, git_root)
        parts = rel_root.split(os.sep)
        if len(parts) == 2 and os.path.basename(root) == "fpv":
            block = parts[0]
            # Exclude flow/fpv
            if not rel_root.startswith("flow/fpv"):
                day = match_day(block)
                day_blocks[day].append(
                    (block, f"//{block}/fpv", False, os.path.join(root, "regr.yaml"))
                )

    # --- Pattern 2: <git root>/flow/fpv/<block> ---
    flow_fpv_dir = os.path.join(git_root, "flow", "fpv")
    if os.path.isdir(flow_fpv_dir):
        for block in os.listdir(flow_fpv_dir):
            block_dir = os.path.join(flow_fpv_dir, block)
            if os.path.isdir(block_dir):
                # For flow_* blocks, match_day will assign them to Thursday (THU)
                day = match_day(f"flow_{block}")
                day_blocks[day].append(
                    (
                        f"flow_{block}",
                        f"//flow/fpv/{block}",
                        True,
                        os.path.join(block_dir, "regr.yaml"),
                    )
                )

    # --- Generate per-block yamls in per-day directories ---
    for day, blocks in day_blocks.items():
        for block, block_dir, is_flow, regr_yaml_path in blocks:
            # Compose output yaml path
            out_yaml = os.path.join(day_dirs[day], f"{block}.yaml")
            # Compose regression_gen args
            args = [
                bin_path,
                "--block",
                block,
                "--directory",
                block_dir,
                "--project",
                "bedrock",
                "--flow-name",
                "jg_fpv",
                "--description",
                f"Bedrock {'flow' if is_flow else ''} FPV regression.",
                # "--no-add-hierarchy",
                "--output",
                out_yaml,
            ]
            # Run regression_gen
            try:
                subprocess.check_call(args)
            except Exception as e:
                print(
                    f"Warning: regression_gen failed for block {block}: {e}",
                    file=sys.stderr,
                )
                continue

            # If the block's regr.yaml exists, add it to the list for import
            if os.path.exists(regr_yaml_path):
                block_yaml_paths[day].append(os.path.abspath(regr_yaml_path))
            # Also add the generated yaml
            block_yaml_paths[day].append(os.path.abspath(out_yaml))

    # --- Generate per-day yaml importers ---
    for day in DAYS:
        day_yaml_dir = day_dirs[day]
        day_yaml = os.path.join(generated_dir, f"Day{day.value}.yaml")
        # Find all .yaml files in the day's directory
        yamls = [
            os.path.join(day_yaml_dir, f)
            for f in os.listdir(day_yaml_dir)
            if f.endswith(".yaml")
        ]
        # Add any extra yamls found (e.g., regr.yaml)
        yamls.extend(block_yaml_paths[day])
        # Remove duplicates and sort
        unique_yamls = sorted(
            set(os.path.abspath(y) for y in yamls if os.path.exists(y))
        )
        # Compute relative paths from day_yaml's directory
        rel_paths = [relative_path(os.path.dirname(day_yaml), y) for y in unique_yamls]
        write_yaml_imports(day_yaml, rel_paths)

    print(
        f"Generated per-day yamls in {generated_dir} and per-block yamls in {generated_dir}/<day>/."
    )


if __name__ == "__main__":
    main()
