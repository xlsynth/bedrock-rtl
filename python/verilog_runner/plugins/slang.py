# SPDX-License-Identifier: Apache-2.0

"""slang elaboration and lint plugins for Verilog Runner."""

import argparse
from dataclasses import dataclass
import shlex
from typing import Dict, Optional, Type

from cli import Elab, Lint, Subcommand, common_args
from eda_tool import EdaTool
from util import (
    gen_file_header,
    get_class_logger,
    include_dirs,
    print_summary,
    run_shell_script,
    write_and_dump_file,
)

PLUGIN_API_VERSION = "2.0.0"


@dataclass
class Slang(EdaTool):
    subcommand: Type[Subcommand] = Elab
    tool_name: str = "slang"
    help: str = "Elaborate a Verilog/SystemVerilog design using slang"
    compile_only: bool = False

    def __post_init__(self):
        self.logger = get_class_logger("elab", "slang")

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        pass

    @classmethod
    def from_args(cls, args):
        return cls(**common_args(args), compile_only=args.compile_only)

    def tcl_preamble(self) -> str:
        return gen_file_header(self.tclfile, "slang")

    def default_tcl_header(self) -> str:
        return ""

    def tcl_analysis_elaborate(self) -> str:
        return ""

    def default_tcl_body(self) -> str:
        return ""

    def tcl_footer(self) -> str:
        return ""

    def slang_args(self) -> list[str]:
        """Returns the arguments shared by slang elaboration and linting."""
        slang_cmd = [
            '"${SLANG_PATH}"',
            "--std 1800-2017",
            "--timescale 1ns/1ps",
            f"-f {self.filelist}",
        ]
        if self.compile_only:
            slang_cmd += ["--lint-only"]
        else:
            slang_cmd += [f"--top {self.top}"]
        slang_cmd += [f"-I{directory}" for directory in include_dirs(self.hdrs)]
        slang_cmd += [f"-D{define}" for define in self.defines]
        slang_cmd += [f"-G{key}={value}" for key, value in self.params.items()]
        slang_cmd += self.opts
        return slang_cmd

    def cmd(self) -> str:
        """Returns a default shell script to run slang."""
        self.logger.info("Generating shell script.")
        cmd = [
            "#!/bin/bash",
            gen_file_header(self.scriptfile, "slang"),
            "set -e",
        ]
        cmd += self.read_env_setup_commands()
        cmd += ["echo ' '"]
        cmd += [
            "echo '----------------------------- slang -----------------------------'"
        ]
        cmd += [" ".join(self.slang_args()), ""]
        return "\n".join(cmd)

    def run_cmd(self) -> Dict[str, bool]:
        """Runs slang and returns its success criteria."""
        self.logger.info("Running shell script.")
        self.prepare_files()
        returncode, shell_output = run_shell_script(self.scriptfile, self.logger)
        write_and_dump_file(shell_output, self.logfile, logger=self.logger)
        return {f"Return code {returncode}": returncode == 0}

    def run_test(self) -> bool:
        """Runs the test and returns True if slang succeeded."""
        self.logger.info("Running test.")
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
class SlangLint(Slang):
    subcommand: Type[Subcommand] = Lint
    help: str = "Lint a Verilog/SystemVerilog design using slang"
    policy: Optional[str] = None

    def __post_init__(self):
        self.logger = get_class_logger("lint", "slang")

    @classmethod
    def from_args(cls, args):
        return cls(**common_args(args), policy=args.policy)

    def slang_args(self) -> list[str]:
        args = super().slang_args()
        if self.policy:
            args.append(f"-F {shlex.quote(self.policy)}")
        return args
