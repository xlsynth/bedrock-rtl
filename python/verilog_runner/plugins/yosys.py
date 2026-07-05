# SPDX-License-Identifier: Apache-2.0

"""Yosys logic-synthesis plugin for Verilog Runner."""

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import shlex
from typing import Dict, List, Optional, Type

from cli import Subcommand, Synth, common_args
from eda_tool import EdaTool
from util import (
    check_filename_extension,
    gen_file_header,
    get_class_logger,
    include_dirs,
    print_summary,
    run_shell_script,
)


PLUGIN_API_VERSION = "2.0.0"
STAT_JSON_BEGIN = "PPA_STAT_JSON_BEGIN"
STAT_JSON_END = "PPA_STAT_JSON_END"
METADATA_JSON_BEGIN = "PPA_METADATA_JSON_BEGIN"
METADATA_JSON_END = "PPA_METADATA_JSON_END"


def _tcl_word(value: object) -> str:
    """Quotes one string as a Tcl list word."""
    text = str(value)
    return "{" + text.replace("\\", "\\\\").replace("}", "\\}") + "}"


def _liberty_file(filename: str) -> str:
    """Validates a Liberty path relative to the configured library root."""
    filename = check_filename_extension(filename, (".lib", ".lib.gz"))
    path = os.path.normpath(filename)
    if os.path.isabs(path) or path == ".." or path.startswith("../"):
        raise argparse.ArgumentTypeError(
            f"Liberty path '{filename}' must be relative to --liberty_root."
        )
    if not re.fullmatch(r"[A-Za-z0-9_./+-]+", path):
        raise argparse.ArgumentTypeError(
            f"Liberty path '{filename}' contains unsupported characters."
        )
    return path


def _liberty_sha256(value: str) -> tuple[str, str]:
    """Parses PATH=SHA256 for one pinned Liberty input."""
    if "=" not in value:
        raise argparse.ArgumentTypeError(
            f"Invalid Liberty checksum '{value}'. Expected PATH=SHA256."
        )
    path, digest = value.split("=", 1)
    path = _liberty_file(path)
    if not re.fullmatch(r"[0-9a-fA-F]{64}", digest):
        raise argparse.ArgumentTypeError(
            f"Invalid SHA-256 digest for Liberty path '{path}'."
        )
    return path, digest.lower()


def _unconstrained_abc_script(clock_period_ps: Optional[int]) -> str:
    """Builds the default-like ABC script used to retain a timing report."""
    map_command = "&nf"
    if clock_period_ps:
        map_command += ",-D," + str(clock_period_ps)
    commands = [
        "+strash",
        "&get,-n",
        "&fraig,-x",
        "&put",
        "scorr",
        "dc2",
        "dretime",
        "strash",
        "&get,-n",
        "&dch,-f",
        map_command,
        "&put",
        "stime,-p",
    ]
    return ";".join(commands)


@dataclass
class Yosys(EdaTool):
    """Runs Yosys synthesis using the yosys-slang SystemVerilog frontend."""

    subcommand: Type[Subcommand] = Synth
    tool_name: str = "yosys"
    help: str = "Synthesize a SystemVerilog design using Yosys and yosys-slang"
    liberties: List[str] = field(default_factory=list)
    sequential_liberty: Optional[str] = None
    liberty_root: Optional[str] = None
    liberty_sha256: Dict[str, str] = field(default_factory=dict)
    synth_profile: str = "generic"
    clock_period_ps: Optional[int] = None
    input_driver_cell: Optional[str] = None
    output_load_ff: Optional[float] = None

    def __post_init__(self):
        self.logger = get_class_logger("synth", "yosys")
        if (self.input_driver_cell is None) != (self.output_load_ff is None):
            raise ValueError(
                "--input_driver_cell and --output_load_ff must be specified together"
            )
        if self.output_load_ff is not None and self.output_load_ff <= 0:
            raise ValueError("--output_load_ff must be greater than zero")
        if self.liberties:
            if not self.liberty_root:
                raise ValueError("--liberty_root is required with --liberty")
            if set(self.liberty_sha256) != set(self.liberties):
                raise ValueError(
                    "--liberty_sha256 must specify exactly one checksum for each --liberty"
                )
            if (
                self.sequential_liberty
                and self.sequential_liberty not in self.liberties
            ):
                raise ValueError(
                    "--sequential_liberty must also be present in --liberty"
                )
        elif (
            self.sequential_liberty
            or self.liberty_root
            or self.liberty_sha256
            or self.clock_period_ps
            or self.input_driver_cell
            or self.output_load_ff
        ):
            raise ValueError(
                "Liberty root, sequential library, checksums, clock period, and I/O constraints require --liberty"
            )

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--liberty",
            type=_liberty_file,
            action="append",
            default=[],
            help="Liberty path relative to --liberty_root. May be repeated.",
        )
        parser.add_argument(
            "--sequential_liberty",
            type=_liberty_file,
            help="Liberty path used for sequential-cell mapping when libraries are split.",
        )
        parser.add_argument(
            "--liberty_root",
            help="Root directory containing the system-provided Liberty files.",
        )
        parser.add_argument(
            "--liberty_sha256",
            type=_liberty_sha256,
            action="append",
            default=[],
            metavar="PATH=SHA256",
            help="Expected checksum for one Liberty path. May be repeated.",
        )
        parser.add_argument(
            "--synth_profile",
            default="generic",
            help="Stable synthesis profile recorded in generated reports.",
        )
        parser.add_argument(
            "--clock_period_ps",
            type=int,
            help="Optional target clock period in picoseconds for technology mapping.",
        )
        parser.add_argument(
            "--input_driver_cell",
            help="Optional Liberty cell assumed to drive each primary input.",
        )
        parser.add_argument(
            "--output_load_ff",
            type=float,
            help="Optional capacitive load in femtofarads on each primary output.",
        )

    @classmethod
    def from_args(cls, args):
        yosys_args = common_args(args)
        yosys_args.update(
            {
                "liberties": args.liberty,
                "sequential_liberty": args.sequential_liberty,
                "liberty_root": args.liberty_root,
                "liberty_sha256": dict(args.liberty_sha256),
                "synth_profile": args.synth_profile,
                "clock_period_ps": args.clock_period_ps,
                "input_driver_cell": args.input_driver_cell,
                "output_load_ff": args.output_load_ff,
            }
        )
        return cls(**yosys_args)

    @property
    def stat_json_file(self) -> str:
        return self.logfile + ".stat.json"

    @property
    def abc_constraints_file(self) -> str:
        return self.logfile + ".abc.constr"

    def tcl_preamble(self) -> str:
        return "\n".join([gen_file_header(self.tclfile, "yosys"), "yosys -import"])

    def default_tcl_header(self) -> str:
        return ""

    def tcl_analysis_elaborate(self) -> str:
        args = ["--single-unit", "--top", self.top]
        args += ["-I" + directory for directory in sorted(include_dirs(self.hdrs))]
        args += ["-D" + define for define in self.defines]
        args += ["-G" + key + "=" + value for key, value in sorted(self.params.items())]
        args += self.opts
        args += self.srcs
        quoted_args = " ".join(_tcl_word(arg) for arg in args)
        return "\n".join(
            [
                "read_slang {*}[list " + quoted_args + "]",
                "hierarchy -check -top " + _tcl_word(self.top),
            ]
        )

    def default_tcl_body(self) -> str:
        # Flatten the complete elaborated hierarchy so all reported statistics
        # and topological paths describe the whole design, not just the top
        # module's immediate contents.
        commands = ["synth -flatten -top " + _tcl_word(self.top)]
        # Measure technology-independent topological depth before mapping.
        # User-defined standard cells are black boxes to ltp and would
        # otherwise collapse mapped paths to zero levels.
        commands.append("ltp -noff " + _tcl_word(self.top))
        stat_args = []
        if self.liberties:
            liberty_paths = [
                _tcl_word(str(Path(self.liberty_root) / path))
                for path in self.liberties
            ]
            if self.sequential_liberty:
                sequential_path = _tcl_word(
                    str(Path(self.liberty_root) / self.sequential_liberty)
                )
                commands.append("dfflibmap -liberty " + sequential_path)

            abc_args = []
            for liberty in liberty_paths:
                abc_args += ["-liberty", liberty]
            if self.input_driver_cell:
                abc_args += ["-constr", _tcl_word(self.abc_constraints_file)]
            if self.clock_period_ps:
                abc_args += ["-D", str(self.clock_period_ps)]
            if not self.input_driver_cell:
                # The default unconstrained Yosys script omits stime. Keep a
                # custom equivalent so the raw report still contains delay.
                abc_script = _unconstrained_abc_script(self.clock_period_ps)
                abc_args += ["-script", _tcl_word(abc_script)]
            commands += ["abc " + " ".join(abc_args), "clean"]
            for liberty in liberty_paths:
                stat_args += ["-liberty", liberty]

        commands += [
            "tee -q -o "
            + _tcl_word(self.stat_json_file)
            + " stat "
            + " ".join(stat_args + ["-json"]),
            "stat " + " ".join(stat_args),
            'puts "PPA_POWER unavailable"',
        ]
        return "\n".join(commands)

    def tcl_footer(self) -> str:
        return ""

    def cmd(self) -> str:
        """Returns a shell script that invokes Yosys."""
        self.logger.info("Generating shell script.")
        preflight = []
        if self.input_driver_cell:
            constraint_lines = [
                "set_driving_cell " + self.input_driver_cell,
                "set_load " + format(self.output_load_ff, "g"),
            ]
            cleanup_command = "rm -f -- " + shlex.quote(self.abc_constraints_file)
            preflight.append("trap " + shlex.quote(cleanup_command) + " EXIT")
            preflight.append(
                "printf '%s\\n' "
                + " ".join(shlex.quote(line) for line in constraint_lines)
                + " > "
                + shlex.quote(self.abc_constraints_file)
            )
        if self.liberties:
            for liberty in self.liberties:
                path = shlex.quote(str(Path(self.liberty_root) / liberty))
                preflight += [
                    "test -r "
                    + path
                    + " || { echo 'Missing system Liberty: '"
                    + path
                    + " >&2; exit 1; }",
                    "printf '%s  %s\\n' '"
                    + self.liberty_sha256[liberty]
                    + "' "
                    + path
                    + " | sha256sum -c -",
                ]
        return "\n".join(
            self.read_env_setup_commands()
            + [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
            ]
            + preflight
            + [
                '"${YOSYS_PATH:-yosys}" -V',
                '"${YOSYS_PATH:-yosys}" -m slang -c "' + self.tclfile + '"',
                "",
            ]
        )

    def run_cmd(self) -> Dict[str, bool]:
        """Runs Yosys and emits the raw report plus delimited JSON statistics."""
        self.logger.info("Running synthesis.")
        self.prepare_files()
        returncode, shell_output = run_shell_script(self.scriptfile, self.logger)

        stat_json = ""
        stat_path = Path(self.stat_json_file)
        if stat_path.exists():
            stat_json = stat_path.read_text(encoding="utf-8", errors="replace")

        report = "\n".join(
            [
                shell_output.rstrip(),
                METADATA_JSON_BEGIN,
                json.dumps(
                    {
                        "input_driver_cell": self.input_driver_cell,
                        "output_load_ff": self.output_load_ff,
                        "clock_period_ps": self.clock_period_ps,
                        "defines": sorted(self.defines),
                        "sequential_liberty": self.sequential_liberty,
                        "liberties": self.liberties,
                        "params": dict(sorted(self.params.items())),
                        "synth_profile": self.synth_profile,
                        "top": self.top,
                    },
                    sort_keys=True,
                ),
                METADATA_JSON_END,
                STAT_JSON_BEGIN,
                stat_json.rstrip(),
                STAT_JSON_END,
                "",
            ]
        )
        Path(self.logfile).write_text(report, encoding="utf-8")
        print(report, end="")
        return {
            f"Return code {returncode}": returncode == 0,
            "Yosys stat JSON generated": bool(stat_json),
        }

    def run_test(self) -> bool:
        """Runs synthesis and returns whether Yosys completed successfully."""
        step_success = self.run_cmd()
        success = all(step_success.values())
        print_summary(
            success=success,
            step_success=step_success,
            report_table="",
            logger=self.logger,
        )
        return success
