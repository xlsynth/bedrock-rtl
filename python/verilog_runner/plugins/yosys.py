# SPDX-License-Identifier: Apache-2.0

"""Yosys logic-synthesis plugin for Verilog Runner."""

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Dict, Type

from cli import Subcommand, Synth, common_args
from eda_tool import EdaTool
from util import (
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


@dataclass
class Yosys(EdaTool):
    """Runs Yosys synthesis using the yosys-slang SystemVerilog frontend."""

    subcommand: Type[Subcommand] = Synth
    tool_name: str = "yosys"
    help: str = "Synthesize a SystemVerilog design using Yosys and yosys-slang"

    def __post_init__(self):
        self.logger = get_class_logger("synth", "yosys")

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        pass

    @classmethod
    def from_args(cls, args):
        return cls(**common_args(args))

    @property
    def stat_json_file(self) -> str:
        return self.logfile + ".stat.json"

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
        stat_args = []
        if self.liberty:
            liberty = _tcl_word(self.liberty)
            commands += [
                "dfflibmap -liberty " + liberty,
                "abc -liberty "
                + liberty
                + (" -D " + str(self.clock_period_ps) if self.clock_period_ps else ""),
                "clean",
            ]
            stat_args = ["-liberty", liberty]

        commands += [
            "tee -q -o "
            + _tcl_word(self.stat_json_file)
            + " stat "
            + " ".join(stat_args + ["-json"]),
            "stat " + " ".join(stat_args),
            "ltp -noff " + _tcl_word(self.top),
            'puts "PPA_POWER unavailable"',
        ]
        return "\n".join(commands)

    def tcl_footer(self) -> str:
        return ""

    def cmd(self) -> str:
        """Returns a shell script that invokes Yosys."""
        self.logger.info("Generating shell script.")
        return "\n".join(
            self.read_env_setup_commands()
            + [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
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
                        "clock_period_ps": self.clock_period_ps,
                        "defines": sorted(self.defines),
                        "liberty": self.liberty,
                        "params": dict(sorted(self.params.items())),
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
