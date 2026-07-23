# SPDX-License-Identifier: Apache-2.0

"""SymbiYosys formal-property-verification plugin for Verilog Runner."""

import argparse
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Dict, Type

from cli import Fpv, Subcommand, common_args
from eda_tool import EdaTool
from util import gen_file_header, get_class_logger, print_summary, run_shell_script


PLUGIN_API_VERSION = "2.0.0"
TASKS = ("prove", "cover")


def _portable_path(path: str) -> PurePosixPath:
    """Returns a portable, relative SBY path."""
    parts = [
        part
        for part in PurePosixPath(Path(path).as_posix()).parts
        if part not in ("", ".", "..", "/")
    ]
    if not parts:
        raise ValueError(f"Cannot create an SBY input path for {path!r}")
    return PurePosixPath(*parts)


def _input_path(path: str) -> str:
    """Returns a portable destination for an SBY HDL input file."""
    return str(PurePosixPath("inputs", _portable_path(path)))


def _data_path(path: str) -> str:
    """Preserves a data file's workspace-relative path in the SBY source tree."""
    return str(_portable_path(path))


@dataclass
class Sby(EdaTool):
    """Runs SymbiYosys prove and cover tasks using yosys-slang and Yices."""

    subcommand: Type[Subcommand] = Fpv
    tool_name: str = "sby"
    help: str = "Prove and cover a SystemVerilog design using SymbiYosys"
    elab_only: bool = False

    def __post_init__(self):
        self.logger = get_class_logger("fpv", "sby")

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        pass

    @classmethod
    def from_args(cls, args):
        unsupported_modes = []
        if args.gui:
            unsupported_modes.append("--gui")
        if args.conn:
            unsupported_modes.append("--conn")
        if unsupported_modes:
            raise ValueError("SBY does not support " + ", ".join(unsupported_modes))
        return cls(
            **common_args(args),
            analysis_opts=args.analysis_opt,
            elab_opts=args.elab_opt,
            elab_only=args.elab_only,
        )

    @property
    def tasks(self) -> tuple[str, ...]:
        return ("elab",) if self.elab_only else TASKS

    @property
    def workdir_prefix(self) -> str:
        return Path(self.tclfile).stem + "_sby"

    def task_status_file(self, task: str) -> Path:
        return Path(f"{self.workdir_prefix}_{task}") / "status"

    def mapped_srcs(self) -> list[str]:
        return [_input_path(src) for src in self.srcs]

    def mapped_hdrs(self) -> list[str]:
        return [_input_path(hdr) for hdr in self.hdrs]

    def tcl_preamble(self) -> str:
        lines = [
            gen_file_header(self.tclfile, "sby"),
            "[tasks]",
            *self.tasks,
            "",
            "[options]",
        ]
        if self.elab_only:
            lines += ["mode prep", "expect pass"]
        else:
            lines += [
                "prove: mode prove",
                "cover: mode cover",
                "depth 20",
                "expect pass",
                "",
                "[engines]",
                "smtbmc yices",
            ]
        return "\n".join(lines)

    def default_tcl_header(self) -> str:
        return ""

    def tcl_analysis_elaborate(self) -> str:
        include_dirs = {"inputs"}
        for header in self.mapped_hdrs():
            parent = PurePosixPath(header).parent
            while str(parent) not in ("", "."):
                include_dirs.add(str(parent))
                parent = parent.parent

        args = ["--single-unit", "--top", self.top]
        args += ["-I" + directory for directory in sorted(include_dirs)]
        args += ["-D" + define for define in self.defines]
        args += ["-G" + key + "=" + value for key, value in sorted(self.params.items())]
        args += self.analysis_opts
        args += self.opts
        args += self.mapped_srcs()
        script_args = " ".join(str(arg) for arg in args)
        hierarchy_args = ["hierarchy", "-check", "-top", self.top]
        hierarchy_args += self.elab_opts
        return "\n".join(
            [
                "[script]",
                "plugin -i slang",
                "read_slang " + script_args,
                " ".join(hierarchy_args),
            ]
        )

    def default_tcl_body(self) -> str:
        return "prep -top " + self.top

    def tcl_footer(self) -> str:
        files = []
        for source, destination in zip(
            self.srcs + self.hdrs, self.mapped_srcs() + self.mapped_hdrs()
        ):
            files.append(destination + " " + source)
        for data_file in self.data:
            files.append(_data_path(data_file) + " " + data_file)
        return "\n".join(["[files]", *files])

    def cmd(self) -> str:
        """Returns a shell script that runs the configured SBY tasks."""
        self.logger.info("Generating shell script.")
        return "\n".join(
            self.read_env_setup_commands()
            + [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
                '"${SBY_PATH:-sby}" --version',
                '"${SBY_PATH:-sby}" -f --prefix "'
                + self.workdir_prefix
                + '" "'
                + self.tclfile
                + '"',
                "",
            ]
        )

    def run_cmd(self) -> Dict[str, bool]:
        """Runs SBY and checks that every configured task reports PASS."""
        self.logger.info("Running formal verification.")
        self.prepare_files()
        returncode, shell_output = run_shell_script(self.scriptfile, self.logger)
        Path(self.logfile).write_text(shell_output, encoding="utf-8")
        print(shell_output, end="" if shell_output.endswith("\n") else "\n")

        step_success = {f"Return code {returncode}": returncode == 0}
        for task in self.tasks:
            status_file = self.task_status_file(task)
            status = "MISSING"
            if status_file.exists():
                status_words = status_file.read_text(
                    encoding="utf-8", errors="replace"
                ).split()
                if status_words:
                    status = status_words[0].upper()
            step_success[f"{task} status {status}"] = status == "PASS"
        return step_success

    def run_test(self) -> bool:
        """Runs SBY and returns whether every expected result passed."""
        step_success = self.run_cmd()
        success = all(step_success.values())
        print_summary(
            success=success,
            step_success=step_success,
            report_table="",
            logger=self.logger,
        )
        return success
