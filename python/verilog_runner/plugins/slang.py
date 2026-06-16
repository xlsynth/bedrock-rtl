# SPDX-License-Identifier: Apache-2.0

"""slang elaboration plugin for Verilog Runner."""

import argparse
from dataclasses import dataclass
from typing import Dict, Type

from cli import Elab, Subcommand, common_args
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

    def __post_init__(self):
        self.logger = get_class_logger("elab", "slang")

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        pass

    @classmethod
    def from_args(cls, args):
        return cls(**common_args(args))

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

    def cmd(self) -> str:
        """Returns a default shell script to run slang."""
        self.logger.info("Generating shell script.")
        slang_cmd = [
            '"${SLANG_PATH}/slang"',
            "--std 1800-2017",
            f"--top {self.top}",
            f"-f {self.filelist}",
        ]
        slang_cmd += [f"-I{directory}" for directory in include_dirs(self.hdrs)]
        slang_cmd += [f"-D{define}" for define in self.defines]
        slang_cmd += [f"-G{key}={value}" for key, value in self.params.items()]
        slang_cmd += self.opts

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
        cmd += [" ".join(slang_cmd), ""]
        return "\n".join(cmd)

    def run_cmd(self) -> Dict[str, bool]:
        """Runs slang and returns its success criteria."""
        self.logger.info("Running shell script.")
        self.prepare_files()
        returncode, shell_output = run_shell_script(self.scriptfile, self.logger)
        write_and_dump_file(shell_output, self.logfile, logger=self.logger)
        return {f"Return code {returncode}": returncode == 0}

    def run_test(self) -> bool:
        """Runs the test and returns True if elaboration succeeded."""
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
