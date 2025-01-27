"""iverilog plugin for Verilog Runner."""

import argparse
from dataclasses import dataclass, field
import textwrap
from typing import Dict, Type

from cli import Sim, Subcommand, common_args
from eda_tool import EdaTool
from util import (
    get_class_logger,
    check_simulation_success,
    gen_file_header,
    include_dirs,
    run_shell_script,
    dump_file,
    write_and_dump_file,
    print_summary,
)

PLUGIN_API_VERSION = "1.1"


@dataclass
class Iverilog(EdaTool):
    subcommand: Type[Subcommand] = Sim
    tool_name: str = "iverilog"
    help: str = "Simulate a Verilog/SystemVerilog design using iverilog"

    def __post_init__(self):
        self.logger = get_class_logger("sim", "iverilog")

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        pass

    @classmethod
    def from_args(cls, args):
        sim_args = {}
        return cls(**common_args(args), **sim_args)

    def tcl_preamble(self) -> str:
        return gen_file_header(self.tclfile, "iverilog")

    def default_tcl_header(self) -> str:
        return ""

    def tcl_analysis_elaborate(self) -> str:
        return ""

    def default_tcl_body(self) -> str:
        tcl_body = ""
        return tcl_body

    def tcl_footer(self) -> str:
        return ""

    def cmd(self) -> str:
        """Returns a default shell script to run iverilog."""
        self.logger.info("Generating shell script.")
        cmd = ["#!/bin/bash"]
        cmd += [gen_file_header(self.scriptfile, "iverilog")]
        cmd += ["set -e"]
        cmd += self.read_env_setup_commands()
        cmd += ["echo ' '"]
        cmd += [
            "echo '--------------------------- iverilog ---------------------------'"
        ]
        iverilog_cmd = [
            "iverilog",
            "-o compiled.vvp",
            "-g2012",
            f"-f{self.filelist}",
            f"-s {self.top}",
        ]
        iverilog_cmd += [f"-I {dir}" for dir in include_dirs(self.hdrs)]
        iverilog_cmd += [f"-D{define}" for define in self.defines]
        iverilog_cmd += [
            f"-P{self.top}.{key}={value}" for key, value in self.params.items()
        ]
        iverilog_cmd += self.opts
        iverilog_cmd = " ".join(iverilog_cmd)
        vvp_cmd = "vvp compiled.vvp"
        cmd += [" && ".join([iverilog_cmd, vvp_cmd])]
        cmd += [""]
        return "\n".join(cmd)

    def run_cmd(self) -> Dict[str, bool]:
        """Runs a shell script and returns a dict of success criteria."""
        self.logger.info("Running shell script.")
        self.prepare_files()
        returncode, shell_output = run_shell_script(self.scriptfile, self.logger)
        write_and_dump_file(shell_output, self.logfile, logger=self.logger)
        return check_simulation_success(returncode, False, shell_output)

    def run_test(self) -> bool:
        """Runs the test and returns True if successful."""
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
