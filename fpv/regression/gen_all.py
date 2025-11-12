#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

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

REGR_TIMEOUT_MINS = 24 * 60  # 24 hours


# --- Configuration ---
class Day(Enum):
    MON = 1
    TUE = 2
    WED = 3
    THU = 4
    FRI = 5
    SAT = 6
    SUN = 7


# Ordered mapping of (regex pattern → Day).
# The order of patterns is significant: the first match wins.
#
# When adding new patterns, append them at the appropriate location to
# express the desired priority.  In particular, put *more specific*
# patterns before more generic ones that could otherwise match the same
# block name.
#
# Examples illustrating the priority rules (requested by the user):
#   • "br_fifo_ext_arb"           → Wednesday (Day.WED)
#   • "br_fifo_shared_dynamic"   → Friday    (Day.FRI)
#   • "br_fifo_shared_pstatic"   → Sunday    (Day.SUN)
#   • "br_fifo"                  → Thursday  (Day.THU)
#
# Any block that does not match one of the patterns below is assigned to
# Day.SUN by default.

DAY_BLOCK_MAP = [
    (r"^amba$", Day.MON),
    (r"^arb$", Day.MON),
    (r"^ecc$", Day.MON),
    (r"^flow_mux$", Day.MON),
    (r"^flow_serializer$", Day.MON),
    (r"^flow_xbar$", Day.MON),
    (r"^cdc$", Day.TUE),
    (r"^tracker$", Day.TUE),
    (r"^counter$", Day.WED),
    (r"^credit$", Day.WED),
    (r"^delay$", Day.WED),
    (r"^flow_.*$", Day.THU),
    (r"^fifo$", Day.FRI),
    (r"^fifo_.*$", Day.FRI),
    (r"^ram$", Day.SAT),
    # FIFO blocks:
    (r"^br_fifo_shared_dynamic$", Day.FRI),
    (r"^br_fifo_shared_pstatic$", Day.SUN),
    (r"^br_fifo_ext_arb$", Day.WED),
    (r"^br_fifo$", Day.THU),
]

DAYS = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI, Day.SAT, Day.SUN]

# ----------------------------------------------------------------------------
# Special (sub-project) FPV directories.
#
# List of tuples: (subdir, block_prefix, is_flow_flag)
#   • subdir        - directory name under <git_root> containing an "fpv" subdir
#   • block_prefix  - string prepended to each discovered block when forming
#                     the logical block name (used for DAY_BLOCK_MAP matching)
#   • is_flow_flag  - whether the discovered block should be treated as a
#                     "flow" block for description purposes.
#
# Add more entries here in the future (e.g. "dma", "serdes", …) and the
# discovery logic below will pick them up automatically without further
# changes.

SPECIAL_FPV_DIRS: list[tuple[str, str, bool]] = [
    ("flow", "flow_", True),  # add prefix "flow_" to logical block name
    ("fifo", "", False),  # keep original block name as-is
]


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


def match_day(block: str) -> Day:
    """Determine the day for a given *block* name by walking the ordered pattern list above.

    The first regular-expression that fully matches the (case insensitive) block name determines the assigned day.
    """
    block_lower = block.lower()
    for pattern, day in DAY_BLOCK_MAP:
        if re.fullmatch(pattern, block_lower):
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
        f.write("\n")
        f.write("invocation_defaults:\n")
        f.write(f"  timeout_mins: {REGR_TIMEOUT_MINS}\n")
        f.write("  metadata:\n")
        f.write('    project: "bedrock"\n')
        f.write('    description: "Bedrock FPV regression."\n')


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

    # Collect all block info: {day: [(block, block_dir, is_flow, regr_yaml_path)]}
    day_blocks = defaultdict(list)
    block_yaml_paths = defaultdict(list)  # {day: [yaml_path, ...]}

    # Track total jobs written across all blocks
    total_jobs_written = 0

    # ----------------------------------------------------------------------------
    # Discover blocks
    # ----------------------------------------------------------------------------

    def discover_top_level_blocks():  # <block>/fpv
        """Yield tuples for ordinary blocks residing at <git_root>/<block>/fpv."""
        for root, _dirs, _files in os.walk(git_root):
            rel_root = os.path.relpath(root, git_root)
            parts = rel_root.split(os.sep)
            if len(parts) != 2 or os.path.basename(root) != "fpv":
                continue

            # Skip directories handled by specialised collectors to avoid duplicates.
            special_roots = tuple(f"{name}/fpv" for name, _, _ in SPECIAL_FPV_DIRS)
            if rel_root.startswith(special_roots):
                continue

            block = parts[0]
            yield block, f"//{block}/fpv", False, os.path.join(root, "regr.yaml")

    def discover_special_blocks(special: str, prefix: str, is_flow: bool):
        """Yield tuples for blocks under <git_root>/<special>/fpv/<block>."""
        special_dir = os.path.join(git_root, special, "fpv")
        if not os.path.isdir(special_dir):
            return
        for block in os.listdir(special_dir):
            block_dir = os.path.join(special_dir, block)
            if not os.path.isdir(block_dir):
                continue
            block_name = f"{prefix}{block}"
            dir_label = f"//{special}/fpv/{block}"
            yield block_name, dir_label, is_flow, os.path.join(block_dir, "regr.yaml")

    # Aggregate discoveries
    for blk, dir_lbl, is_flow, regr_yaml in discover_top_level_blocks():
        day = match_day(blk)
        day_blocks[day].append((blk, dir_lbl, is_flow, regr_yaml))

    # Handle all specialised FPV directories declared in SPECIAL_FPV_DIRS.
    for special, prefix, is_flow_flag in SPECIAL_FPV_DIRS:
        for blk, dir_lbl, is_flow, regr_yaml in discover_special_blocks(
            special, prefix, is_flow_flag
        ):
            day = match_day(blk)
            day_blocks[day].append((blk, dir_lbl, is_flow, regr_yaml))

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

            # For any block discovered from a special FPV directory, we want a
            # non-recursive Bazel query because each BUILD file already
            # enumerates the targets within that package.
            if any(
                block_dir.startswith(f"//{name}/fpv/")
                for name, _, _ in SPECIAL_FPV_DIRS
            ):
                args.append("--non-recursive")

            # Run regression_gen and capture its output so we can parse the job
            # count written.  We still echo the output to the console for
            # transparency.
            try:
                completed = subprocess.run(
                    args,
                    check=True,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                )
            except subprocess.CalledProcessError as e:
                # Forward captured output before exiting.
                print(e.stdout or "", end="", file=sys.stderr)
                print(
                    f"Warning: regression_gen failed for block {block}: {e}",
                    file=sys.stderr,
                )
                continue

            # Echo regression_gen output
            print(completed.stdout, end="")

            # Parse "Wrote N jobs" line
            m = re.search(r"Wrote\s+(\d+)\s+jobs", completed.stdout)
            if m:
                total_jobs_written += int(m.group(1))

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

    # ---------------------------------------------------------------------
    # Sanity-check: ensure total jobs == overall workspace jobs of the rule
    # kind we care about.
    # ---------------------------------------------------------------------

    try:
        workspace_labels = subprocess.check_output(
            [
                "bazel",
                "query",
                "--output=label",
                'kind("rule_verilog_fpv_sandbox rule", //...)',
            ],
            encoding="utf-8",
        )
        total_jobs_workspace = len(
            [l for l in workspace_labels.splitlines() if l.strip()]
        )
    except Exception:
        total_jobs_workspace = None

    if total_jobs_workspace is not None and total_jobs_written != total_jobs_workspace:
        print(
            f"Warning: job count mismatch - generated {total_jobs_written} jobs, "
            f"but Bazel query found {total_jobs_workspace}.",
            file=sys.stderr,
        )
    else:
        print(f"Verified total job count: {total_jobs_written} jobs.")


if __name__ == "__main__":
    main()
