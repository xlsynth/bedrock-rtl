#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Inventory RTL modules that lack direct or transitive simulation coverage.

This script intentionally uses Bazel query for dependency closure. It only uses
Python for candidate RTL discovery, direct-bench name matching, and table
formatting.
"""

import argparse
import collections
import pathlib
import re
import subprocess
import sys
from typing import Dict, List, Set


DEFAULT_OUTPUT_USER_ROOT = "/mnt/scratch/.cache/bazel"

# These benches intentionally exercise more than one DUT, or use a bench name
# that is not a simple "<module>_tb" spelling.
COMPOSITE_DIRECT_BENCH_PREFIXES = {
    "//credit/rtl:br_credit_sender_vc": ("br_credit_sender_vc_rr",),
    "//ecc/rtl:br_ecc_secded_decoder": ("br_ecc_secded_encoder_decoder",),
    "//ecc/rtl:br_ecc_secded_encoder": ("br_ecc_secded_encoder_decoder",),
    "//ecc/rtl:br_ecc_sed_decoder": ("br_ecc_sed_encoder_decoder",),
    "//ecc/rtl:br_ecc_sed_encoder": ("br_ecc_sed_encoder_decoder",),
    "//enc/rtl:br_enc_bin2gray": ("br_enc_gray",),
    "//enc/rtl:br_enc_gray2bin": ("br_enc_gray",),
    "//flow/rtl:br_flow_buffer": ("br_flow_buffer_depth_",),
    "//flow/rtl:br_flow_demux_select": ("br_flow_demux_select",),
    "//flow/rtl:br_flow_demux_select_unstable": ("br_flow_demux_select",),
    "//flow/rtl:br_flow_fork": ("br_flow_fork",),
    "//flow/rtl:br_flow_fork_select_multihot": ("br_flow_fork_select_multihot",),
    "//flow/rtl:br_flow_join": ("br_flow_join",),
    "//flow/rtl:br_flow_mux_select": ("br_flow_mux_select",),
    "//flow/rtl:br_flow_mux_select_unstable": ("br_flow_mux_select",),
    "//ram/rtl:br_ram_flops": ("br_ram_flops_1r1w",),
    "//ram/rtl:br_ram_flops_1r1w_mock": ("br_ram_flops_1r1w",),
}

# Package/helper RTL files that are not modules needing standalone benches.
EXCLUDED_RTL_STEMS = {
    "br_lfsr_taps",
}


def run_bazel_query(args: argparse.Namespace, expression: str) -> Set[str]:
    cmd = [args.bazel]
    if args.bazel_output_user_root:
        cmd.append(f"--output_user_root={args.bazel_output_user_root}")
    cmd.extend(["query", expression])

    proc = subprocess.run(
        cmd,
        cwd=args.workspace,
        check=False,
        encoding="utf-8",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)

    return {
        line.strip()
        for line in proc.stdout.splitlines()
        if line.strip() and not line.startswith(("Loading:", "INFO:"))
    }


def rtl_candidates(workspace: pathlib.Path) -> Dict[str, pathlib.Path]:
    candidates = {}  # type: Dict[str, pathlib.Path]
    for path in sorted(workspace.glob("*/rtl/*.sv")):
        area = path.parts[-3]
        stem = path.stem
        if area == "gate":
            continue
        if stem.endswith("_pkg") or stem in EXCLUDED_RTL_STEMS:
            continue

        label = f"//{area}/rtl:{stem}"
        candidates[label] = path.relative_to(workspace)
    return candidates


def sim_test_names(sim_tests: Set[str]) -> Set[str]:
    names = set()
    for label in sim_tests:
        if "/sim" not in label:
            continue
        try:
            names.add(label.split(":", 1)[1])
        except IndexError:
            pass
    return names


def has_direct_bench(label: str, test_names: Set[str]) -> bool:
    stem = label.split(":", 1)[1]
    simple_prefix = re.compile(
        rf"^{re.escape(stem)}(?:_tb|_gen_tb|_gen_unittest|_sim_test_tools_suite)"
    )
    if any(simple_prefix.match(name) for name in test_names):
        return True

    for prefix in COMPOSITE_DIRECT_BENCH_PREFIXES.get(label, ()):
        if any(name.startswith(prefix) for name in test_names):
            return True

    return False


def render_list(paths: List[pathlib.Path]) -> str:
    if not paths:
        return "0"
    names = ", ".join(f"`{path.name}`" for path in paths)
    return f"{len(paths)}: {names}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workspace",
        type=pathlib.Path,
        default=pathlib.Path.cwd(),
        help="Bazel workspace root. Defaults to the current directory.",
    )
    parser.add_argument(
        "--bazel",
        default="bazel",
        help="Bazel executable. Defaults to 'bazel'.",
    )
    parser.add_argument(
        "--bazel-output-user-root",
        default=DEFAULT_OUTPUT_USER_ROOT,
        help=(
            "Bazel output_user_root. Defaults to "
            f"{DEFAULT_OUTPUT_USER_ROOT!r}; pass '' to use Bazel's default."
        ),
    )
    args = parser.parse_args()
    args.workspace = args.workspace.resolve()

    sim_test_query = 'filter("_sim_test$", tests(//...))'
    sim_closure_query = (
        'kind("verilog_library rule", deps(filter("_sim_test$", tests(//...))))'
    )

    sim_tests = run_bazel_query(args, sim_test_query)
    sim_closure = run_bazel_query(args, sim_closure_query)
    test_names = sim_test_names(sim_tests)
    candidates = rtl_candidates(args.workspace)

    rows = collections.defaultdict(
        lambda: {"indirect": [], "none": []}
    )  # type: Dict[str, Dict[str, List[pathlib.Path]]]
    for label, path in candidates.items():
        if has_direct_bench(label, test_names):
            continue

        area = path.parts[0]
        if label in sim_closure:
            rows[area]["indirect"].append(path)
        else:
            rows[area]["none"].append(path)

    indirect_count = sum(len(row["indirect"]) for row in rows.values())
    none_count = sum(len(row["none"]) for row in rows.values())
    total = indirect_count + none_count

    print(
        f"Summary: {total} modules lack a direct DUT bench; "
        f"{indirect_count} are in a sim-test library closure, "
        f"and {none_count} are missing from all sim-test library closures."
    )
    print()
    print(
        "| Area | Only missing a direct DUT bench, but in sim closure "
        "| Missing from all sim-test library closures |"
    )
    print("|---|---:|---:|")
    for area in sorted(rows):
        row = rows[area]
        print(
            f"| `{area}` | {render_list(row['indirect'])} "
            f"| {render_list(row['none'])} |"
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
