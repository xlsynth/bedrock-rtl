# SPDX-License-Identifier: Apache-2.0

"""Yosys synthesis and SymbiYosys formal plugins for Verilog Runner."""

import argparse
from dataclasses import dataclass, field
import json
from pathlib import Path
import shlex
from typing import Dict, Type

from cli import Fpv, Subcommand, Synth, common_args
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
        """Runs the selected Yosys flow and reports its success criteria."""
        step_success = self.run_cmd()
        success = all(step_success.values())
        print_summary(
            success=success,
            step_success=step_success,
            report_table="",
            logger=self.logger,
        )
        return success


@dataclass
class YosysFpv(Yosys):
    """Checks safety properties with yosys-slang and SymbiYosys.

    ``opts`` contains SBY settings in ``key=value`` form. Supported keys are
    ``mode`` (prove, bmc, cover), ``engine``, ``depth``, and ``timeout`` in seconds.
    Frontend switches use ``analysis_opts`` and ``elab_opts``. Clock and reset
    assumptions belong in the formal harness.
    """

    subcommand: Type[Subcommand] = Fpv
    help: str = "Check SystemVerilog properties using Yosys and SymbiYosys"
    analysis_opts: list[str] = field(default_factory=list)
    elab_only: bool = False
    sby_options: Dict[str, str] = field(init=False)
    engine: str = field(init=False)

    def __post_init__(self):
        self.logger = get_class_logger("fpv", "yosys")
        settings = {"mode": "prove", "depth": "20", "timeout": "60"}
        for option in self.opts:
            key, separator, value = option.partition("=")
            if (
                not separator
                or key not in ("mode", "engine", "depth", "timeout")
                or not value
                or "\n" in value
                or "\r" in value
            ):
                raise ValueError("Invalid Yosys FPV option: " + option)
            settings[key] = value
        if settings["mode"] not in ("prove", "bmc", "cover"):
            raise ValueError("Yosys FPV mode must be prove, bmc, or cover")
        for key in ("depth", "timeout"):
            if not settings[key].isdigit() or int(settings[key]) < 1:
                raise ValueError("Yosys FPV " + key + " must be a positive integer")
        self.engine = settings.pop(
            "engine", "abc pdr" if settings["mode"] == "prove" else "smtbmc z3"
        )
        self.sby_options = settings
        self.opts = (
            ["--no-synthesis-define", "-DFORMAL"] + self.analysis_opts + self.elab_opts
        )

    @classmethod
    def from_args(cls, args):
        if args.gui or args.conn:
            raise ValueError("Yosys FPV supports batch property verification")
        return cls(
            **common_args(args),
            analysis_opts=args.analysis_opt,
            elab_opts=args.elab_opt,
            elab_only=args.elab_only,
        )

    @property
    def model_file(self) -> str:
        return self.tclfile + ".il"

    @property
    def sby_file(self) -> str:
        return self.tclfile + ".sby"

    @property
    def work_directory(self) -> str:
        return self.tclfile + ".sby-work"

    def default_tcl_body(self) -> str:
        return "prep -top " + _tcl_word(self.top)

    def tcl_footer(self) -> str:
        return "write_rtlil " + _tcl_word(self.model_file)

    def sby_config(self) -> str:
        # The RTLIL model already includes the transitive sources, headers,
        # defines, and top-level parameter overrides from the runner.
        return "\n".join(
            ["[options]"]
            + [key + " " + value for key, value in self.sby_options.items()]
            + [
                "[engines]",
                self.engine,
                "[script]",
                "read_rtlil model.il",
                "prep -top " + self.top,
                "[files]",
                "model.il " + self.model_file,
                "",
            ]
        )

    def cmd(self) -> str:
        commands = (
            [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
            ]
            + self.read_env_setup_commands()
            + [
                '"${YOSYS_PATH:-yosys}" -m slang -c ' + shlex.quote(self.tclfile),
            ]
        )
        if not self.elab_only:
            # Embed the SBY configuration so existing sandbox rules need only
            # package the runner's Tcl, shell script, and source file list.
            commands += [
                "cat > " + shlex.quote(self.sby_file) + " <<'VERILOG_RUNNER_SBY'",
                self.sby_config(),
                "VERILOG_RUNNER_SBY",
                "sby_backup_args=()",
                "if [ -d " + shlex.quote(self.work_directory) + " ]; then",
                "  sby_backup_args=(-b)",
                "fi",
                '"${SBY_PATH:-sby}" --yosys "${YOSYS_PATH:-yosys}" "${sby_backup_args[@]}" -j 1 -d '
                + shlex.quote(self.work_directory)
                + " "
                + shlex.quote(self.sby_file),
            ]
        return "\n".join(commands + [""])

    def run_cmd(self) -> Dict[str, bool]:
        self.prepare_files()
        returncode, output = run_shell_script(self.scriptfile, self.logger)
        Path(self.logfile).write_text(output, encoding="utf-8")
        print(output, end="")
        success = {f"Return code {returncode}": returncode == 0}
        if not self.elab_only:
            status_file = Path(self.work_directory) / "status"
            fields = status_file.read_text().split() if status_file.exists() else []
            verdict = fields[0] if fields else "MISSING"
            success["SymbiYosys status " + verdict] = verdict == "PASS"
        return success
