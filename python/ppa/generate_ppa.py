#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Runs tagged Bazel synthesis targets and regenerates PPA reports."""

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Iterable, Optional


METADATA_JSON_BEGIN = "PPA_METADATA_JSON_BEGIN"
METADATA_JSON_END = "PPA_METADATA_JSON_END"
STAT_JSON_BEGIN = "PPA_STAT_JSON_BEGIN"
STAT_JSON_END = "PPA_STAT_JSON_END"
EXCLUDED_DOCUMENTED_TOPS = {
    "br_amba",
    "br_cdc_pkg",
    "br_ecc_secded",
    "br_lfsr_taps",
    "br_math",
    "br_ram_flops_1r1w_mock",
}

PROFILE_GENERIC = "generic"
PROFILE_ASAP7_RVT_TT = "asap7-rvt-tt"
PROFILE_CONFIG = {
    PROFILE_GENERIC: {
        "tag": "ppa-synth-generic",
        "output": "PPA.md",
    },
    PROFILE_ASAP7_RVT_TT: {
        "tag": "ppa-synth-asap7-rvt-tt",
        "output": "PPA_ASAP7_RVT_TT.md",
    },
}


@dataclass(frozen=True)
class PpaMetrics:
    target: str
    top: str
    params: dict[str, str]
    synth_profile: str
    tool_version: str
    liberties: tuple[str, ...]
    abc_driver_cell: Optional[str]
    abc_load_ff: Optional[float]
    cells: int
    flops: int
    wire_bits: int
    logic_depth: Optional[int]
    mapped_area: Optional[float]
    mapped_delay: Optional[float]


def _delimited(text: str, begin: str, end: str) -> str:
    match = re.search(
        re.escape(begin) + r"\s*(.*?)\s*" + re.escape(end), text, re.DOTALL
    )
    if not match:
        raise ValueError(f"missing {begin}/{end} report markers")
    return match.group(1)


def _load_embedded_json(text: str, begin: str, end: str) -> dict:
    payload = _delimited(text, begin, end)
    first = payload.find("{")
    last = payload.rfind("}")
    if first < 0 or last < first:
        raise ValueError(f"no JSON object between {begin}/{end}")
    return json.loads(payload[first : last + 1])


def _module_stats(stats: dict, top: str) -> dict:
    modules = stats.get("modules", {})
    for name, values in modules.items():
        if name.lstrip("\\") == top:
            return values
    if len(modules) == 1:
        return next(iter(modules.values()))
    raise ValueError(f"Yosys statistics do not contain top module {top!r}")


def _first_float(patterns: Iterable[str], text: str) -> Optional[float]:
    for pattern in patterns:
        matches = re.findall(pattern, text, re.IGNORECASE)
        if matches:
            return float(matches[-1])
    return None


def parse_log(target: str, text: str) -> PpaMetrics:
    """Parses one raw Verilog Runner/Yosys log."""
    metadata = _load_embedded_json(text, METADATA_JSON_BEGIN, METADATA_JSON_END)
    stats = _load_embedded_json(text, STAT_JSON_BEGIN, STAT_JSON_END)
    top = metadata["top"]
    module = _module_stats(stats, top)
    cells_by_type = module.get("num_cells_by_type", {})
    flops = sum(
        int(count)
        for cell_type, count in cells_by_type.items()
        if "dff" in cell_type.lower() or cell_type.lower() in {"$ff", "$_ff_"}
    )

    version_match = re.search(r"^Yosys\s+(.+)$", text, re.MULTILINE)
    depth_matches = re.findall(
        r"Longest topological path.*?length\s*=?\s*(\d+)", text, re.IGNORECASE
    )
    mapped_area = _first_float(
        [
            r"Chip area for module .*?:\s*([0-9.eE+-]+)",
            r"ABC:.*?area\s*=\s*([0-9.eE+-]+)",
        ],
        text,
    )
    mapped_delay = _first_float(
        [r"ABC:.*?delay\s*=\s*([0-9.eE+-]+)"],
        text,
    )

    return PpaMetrics(
        target=target,
        top=top,
        params={str(k): str(v) for k, v in metadata.get("params", {}).items()},
        synth_profile=str(metadata.get("synth_profile", PROFILE_GENERIC)),
        tool_version=version_match.group(0).strip() if version_match else "unknown",
        liberties=tuple(str(path) for path in metadata.get("liberties", [])),
        abc_driver_cell=metadata.get("abc_driver_cell"),
        abc_load_ff=(
            float(metadata["abc_load_ff"])
            if metadata.get("abc_load_ff") is not None
            else None
        ),
        cells=int(module.get("num_cells", 0)),
        flops=flops,
        wire_bits=int(module.get("num_wire_bits", 0)),
        logic_depth=int(depth_matches[-1]) if depth_matches else None,
        mapped_area=mapped_area,
        mapped_delay=mapped_delay,
    )


def _markdown(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def _optional_number(value: Optional[float | int]) -> str:
    if value is None:
        return "N/A"
    if isinstance(value, float):
        return f"{value:g}"
    return str(value)


def render_markdown(
    metrics: Iterable[PpaMetrics], profile: Optional[str] = None
) -> str:
    """Renders deterministic Markdown for the collected metrics."""
    rows = sorted(
        metrics, key=lambda metric: (metric.top, sorted(metric.params.items()))
    )
    profiles = {metric.synth_profile for metric in rows}
    if profile is None:
        if len(profiles) != 1:
            raise ValueError(f"expected one synthesis profile, got {sorted(profiles)}")
        profile = next(iter(profiles))
    if profiles and profiles != {profile}:
        raise ValueError(
            f"metrics for profiles {sorted(profiles)} cannot render as {profile}"
        )

    versions = sorted({metric.tool_version for metric in rows})
    lines = [
        "<!-- Auto-generated by //python/ppa:generate_ppa. Do not edit manually. -->",
        "",
    ]
    if profile == PROFILE_GENERIC:
        lines += [
            "# Bedrock RTL synthesis signals",
            "",
            "These technology-independent Yosys results are intended for quick relative "
            "comparisons. Cell count is an area proxy and combinational logic depth is a "
            "timing proxy. Physical area, delay, and power require a characterized library, "
            "constraints, and activity data. Gate-dependent designs use the behavioral gate "
            "model for logical estimation only.",
        ]
    elif profile == PROFILE_ASAP7_RVT_TT:
        liberties = sorted(
            {Path(path).name for metric in rows for path in metric.liberties}
        )
        driver_cells = {metric.abc_driver_cell for metric in rows}
        output_loads = {metric.abc_load_ff for metric in rows}
        if len(driver_cells) != 1 or None in driver_cells:
            raise ValueError("ASAP7 metrics must use one ABC input driver cell")
        if len(output_loads) != 1 or None in output_loads:
            raise ValueError("ASAP7 metrics must use one ABC output load")
        driver_cell = next(iter(driver_cells))
        output_load = next(iter(output_loads))
        lines += [
            "# Bedrock RTL synthesis signals — ASAP7 RVT/TT",
            "",
            (
                "These Yosys/ABC results use the ASAP7 7.5-track regular-threshold-voltage "
                "standard-cell libraries at the typical process and temperature corner. "
                "They are quick comparative synthesis estimates, not signoff results."
            ),
            "",
            "Library source: OpenROAD-flow-scripts commit `ae9a8ed9d67b087abffd4645208672a33da2d3bf`.",
            "",
            "Library files: "
            + ", ".join(f"`{_markdown(path)}`" for path in liberties)
            + ".",
            "",
            (
                f"ABC mapping assumes `{_markdown(driver_cell)}` drives each primary input "
                f"and applies {output_load:g} fF to each primary output. Mapping runs "
                "`buffer`, `upsize`, and `dnsize` before `stime -p`; no clock delay target "
                "is imposed, and `WireLoad = none`."
            ),
        ]
    else:
        raise ValueError(f"unknown synthesis profile: {profile}")

    lines += [
        "",
        "Tool versions: " + (", ".join(f"`{_markdown(v)}`" for v in versions) or "N/A"),
        "",
        "## Metric definitions",
        "",
        (
            "The design hierarchy is flattened before measurement, so these metrics cover "
            "the complete elaborated top and all of its submodules."
        ),
        "",
    ]
    if profile == PROFILE_GENERIC:
        lines += [
            "- **Cells:** Total post-synthesis Yosys cell instances. Without a Liberty "
            "library, combinational logic is mapped to Yosys generic gates, so every gate, "
            "mux, flip-flop, and other remaining cell counts as one regardless of physical "
            "area or drive strength.",
            "- **Flops:** The subset of cells recognized as generic flip-flops. Memories "
            "implemented from registers, including flop RAMs, contribute to this count "
            "after Yosys lowers them to flip-flop cells.",
            "- **Wire bits:** Total post-synthesis RTLIL signal bits, including ports and "
            "internal nets. This is a netlist-complexity signal, not physical wire length, "
            "routing congestion, capacitance, or fanout.",
            "- **Logic depth:** Longest topological chain of generic combinational cells "
            "reported by `ltp -noff`. Flip-flops delimit paths, and every cell is one level; "
            "the value is not a time measurement.",
            "",
            "| Top | Parameters | Cells | Flops | Wire bits | Logic depth | Mapped area | Mapped delay | Power | Bazel target |",
            "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |",
        ]
    else:
        lines += [
            "- **Mapped cells:** Total ASAP7 standard-cell instances after `dfflibmap` and ABC mapping.",
            "- **Mapped flops:** Mapped cell instances whose ASAP7 cell name identifies a DFF. Flop RAMs contribute one mapped DFF per stored bit.",
            "- **Wire bits:** Post-mapping RTLIL signal bits. This is netlist complexity, not physical wire length, routing congestion, capacitance, or fanout.",
            "- **Generic logic depth:** Longest topological generic combinational-cell chain measured before technology mapping. It is retained as a structural comparison and is not a time value.",
            "- **Liberty area:** Sum of mapped cells' Liberty `area` values. It excludes SRAM macros, wiring, placement, routing, clock trees, and physical overhead.",
            "- **ABC delay:** Longest combinational delay estimated by ABC `stime -p` from the mapped Liberty timing tables, in picoseconds, under the assumptions above.",
            "- **Power:** Unavailable because this flow has neither switching activity nor an activity-aware power-analysis engine.",
            "",
            "| Top | Parameters | Mapped cells | Mapped flops | Wire bits | Generic logic depth | Liberty area | ABC delay (ps) | Power | Bazel target |",
            "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |",
        ]
    for metric in rows:
        params = ", ".join(
            f"{key}={value}" for key, value in sorted(metric.params.items())
        )
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{_markdown(metric.top)}`",
                    f"`{_markdown(params or '<defaults>')}`",
                    str(metric.cells),
                    str(metric.flops),
                    str(metric.wire_bits),
                    _optional_number(metric.logic_depth),
                    _optional_number(metric.mapped_area),
                    _optional_number(metric.mapped_delay),
                    "N/A",
                    f"`{_markdown(metric.target)}`",
                ]
            )
            + " |"
        )

    lines += [
        "",
        "## Intentional exclusions",
        "",
        "- Package-only libraries (`br_amba`, `br_cdc_pkg`, `br_ecc_secded`, `br_lfsr_taps`, and `br_math`) have no module top.",
        "- `br_ram_flops_1r1w_mock` is a simulation-only RAM model and intentionally rejects synthesis.",
        "",
    ]
    return "\n".join(lines)


def documented_module_tops(libraries_doc: Path) -> set[str]:
    """Returns the documented public br_* library entries."""
    return set(
        re.findall(
            r"^\|\s+`(br_[^`]+)`\s*(?:\||$)",
            libraries_doc.read_text(encoding="utf-8"),
            re.MULTILINE,
        )
    )


def validate_catalog_coverage(
    metrics: Iterable[PpaMetrics], libraries_doc: Path
) -> None:
    expected = documented_module_tops(libraries_doc)
    expected = {top for top in expected if top not in EXCLUDED_DOCUMENTED_TOPS}
    actual = {metric.top for metric in metrics}
    missing = sorted(expected - actual)
    if missing:
        raise ValueError(
            "documented public tops without PPA sweeps: " + ", ".join(missing)
        )


def _bazel_command(bazel: str, output_base: Optional[Path], *args: str) -> list[str]:
    command = [bazel]
    if output_base:
        command.append("--output_base=" + str(output_base))
    return command + list(args)


def query_targets(
    workspace: Path, bazel: str, output_base: Optional[Path], profile_tag: str
) -> list[str]:
    query = (
        f'attr(tags, "ppa-synth", attr(tags, "{profile_tag}", //...)) '
        'except attr(tags, "ppa-synth-sandbox", //...)'
    )
    proc = subprocess.run(
        _bazel_command(
            bazel,
            output_base,
            "query",
            query,
            "--output=label",
        ),
        cwd=workspace,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode:
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return sorted(line for line in proc.stdout.splitlines() if line.startswith("//"))


def _log_filename(target: str) -> str:
    return target.removeprefix("//").replace("/", "__").replace(":", "__") + ".log"


def _cleanup_runner_outputs(workspace: Path, target: str) -> None:
    name = target.rsplit(":", 1)[-1]
    for suffix in (".f", ".tcl", ".sh", ".log", ".log.stat.json"):
        path = workspace / (name + suffix)
        if path.exists():
            path.unlink()


def run_target(
    workspace: Path,
    bazel: str,
    output_base: Optional[Path],
    target: str,
    logs_dir: Path,
) -> PpaMetrics:
    proc = subprocess.run(
        _bazel_command(bazel, output_base, "run", "--noshow_progress", target),
        cwd=workspace,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    log = "\n".join([proc.stdout, proc.stderr])
    (logs_dir / _log_filename(target)).write_text(log, encoding="utf-8")
    _cleanup_runner_outputs(workspace, target)
    if proc.returncode:
        sys.stderr.write(log)
        raise RuntimeError(f"synthesis target failed: {target}")
    return parse_log(target, log)


def collect_metrics(
    workspace: Path,
    bazel: str,
    output_base: Optional[Path],
    targets: list[str],
    logs_dir: Path,
    resume: bool = False,
) -> list[PpaMetrics]:
    metrics = []
    seen = set()
    for index, target in enumerate(targets, start=1):
        log_path = logs_dir / _log_filename(target)
        metric = None
        if resume and log_path.exists():
            try:
                metric = parse_log(target, log_path.read_text(encoding="utf-8"))
            except (json.JSONDecodeError, KeyError, TypeError, ValueError):
                pass
        state = "cached" if metric else "run"
        print(f"[{index}/{len(targets)}] [{state}] {target}", flush=True)
        if metric is None:
            metric = run_target(workspace, bazel, output_base, target, logs_dir)
        key = (metric.top, tuple(sorted(metric.params.items())))
        if key in seen:
            raise ValueError(
                f"duplicate top/parameter configuration: {metric.top} {metric.params}"
            )
        seen.add(key)
        metrics.append(metric)
    return metrics


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bazel", default="bazel")
    parser.add_argument(
        "--bazel-output-base",
        type=Path,
        help="Bazel output base for child commands (normally selected automatically).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail instead of updating stale PPA reports.",
    )
    parser.add_argument(
        "--logs-dir", type=Path, help="Preserve raw per-target logs in this directory."
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Reuse successfully parsed logs from --logs-dir before running a target.",
    )
    parser.add_argument(
        "--target",
        action="append",
        default=[],
        help="Run only this label; repeat as needed.",
    )
    parser.add_argument(
        "--profile",
        action="append",
        choices=sorted(PROFILE_CONFIG),
        default=[],
        help="Generate only this profile; repeat as needed. Defaults to all profiles.",
    )
    parser.add_argument("--workspace", type=Path)
    args = parser.parse_args()
    if args.resume and not args.logs_dir:
        parser.error("--resume requires --logs-dir")

    workspace = (
        args.workspace or Path(os.environ.get("BUILD_WORKSPACE_DIRECTORY", Path.cwd()))
    ).resolve()
    bazel_output_base = args.bazel_output_base
    if bazel_output_base:
        bazel_output_base = bazel_output_base.expanduser().resolve()
    elif os.environ.get("BUILD_WORKSPACE_DIRECTORY"):
        # `bazel run` keeps its server command active while this program runs.
        # Use a stable second output base so nested Bazel commands do not wait
        # forever on the parent server lock, while retaining cache reuse.
        bazel_output_base = Path.home() / ".cache" / "bedrock-rtl-ppa-bazel"

    if args.target:
        if args.logs_dir:
            logs_dir = args.logs_dir.resolve()
            logs_dir.mkdir(parents=True, exist_ok=True)
            metrics = collect_metrics(
                workspace,
                args.bazel,
                bazel_output_base,
                sorted(args.target),
                logs_dir,
                resume=args.resume,
            )
        else:
            with tempfile.TemporaryDirectory(prefix="bedrock-ppa-") as temporary:
                metrics = collect_metrics(
                    workspace,
                    args.bazel,
                    bazel_output_base,
                    sorted(args.target),
                    Path(temporary),
                )
        # Explicit targets are a development aid for exercising the runner and
        # parser. A partial result must never replace the checked-in catalog.
        print(render_markdown(metrics))
        return 0

    profiles = args.profile or list(PROFILE_CONFIG)
    temporary_logs = None
    if args.logs_dir:
        logs_root = args.logs_dir.resolve()
    else:
        temporary_logs = tempfile.TemporaryDirectory(prefix="bedrock-ppa-")
        logs_root = Path(temporary_logs.name)

    stale = False
    try:
        for profile in profiles:
            config = PROFILE_CONFIG[profile]
            targets = query_targets(
                workspace, args.bazel, bazel_output_base, config["tag"]
            )
            if not targets:
                raise SystemExit(f"no ppa-synth targets found for {profile}")

            logs_dir = logs_root / profile
            logs_dir.mkdir(parents=True, exist_ok=True)
            metrics = collect_metrics(
                workspace,
                args.bazel,
                bazel_output_base,
                targets,
                logs_dir,
                resume=args.resume,
            )
            metric_profiles = {metric.synth_profile for metric in metrics}
            if metric_profiles != {profile}:
                raise ValueError(
                    f"{profile} targets reported profiles {sorted(metric_profiles)}"
                )
            validate_catalog_coverage(metrics, workspace / "LIBRARIES.md")
            rendered = render_markdown(metrics, profile)
            output = workspace / config["output"]
            if args.check:
                if (
                    not output.exists()
                    or output.read_text(encoding="utf-8") != rendered
                ):
                    print(
                        f"{output} is stale; run bazel run //python/ppa:generate_ppa",
                        file=sys.stderr,
                    )
                    stale = True
            else:
                output.write_text(rendered, encoding="utf-8")
                print(f"Wrote {output}")
    finally:
        if temporary_logs:
            temporary_logs.cleanup()
    return 1 if stale else 0


if __name__ == "__main__":
    raise SystemExit(main())
