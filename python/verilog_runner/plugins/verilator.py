# SPDX-License-Identifier: Apache-2.0

"""Verilator plugin for Verilog Runner."""

import argparse
from dataclasses import dataclass
from typing import Dict, Type

from cli import Sim, Subcommand, common_args
from eda_tool import EdaTool
from util import (
    check_simulation_success,
    gen_file_header,
    get_class_logger,
    include_dirs,
    print_summary,
    run_shell_script,
    write_and_dump_file,
)

PLUGIN_API_VERSION = "2.0.0"


@dataclass
class Verilator(EdaTool):
    subcommand: Type[Subcommand] = Sim
    tool_name: str = "verilator"
    help: str = "Simulate a Verilog/SystemVerilog design using Verilator"
    elab_only: bool = False
    waves: bool = False

    def __post_init__(self):
        self.logger = get_class_logger("sim", "verilator")

    @classmethod
    def add_args(cls, parser: argparse.ArgumentParser) -> None:
        pass

    @classmethod
    def from_args(cls, args):
        sim_args = {
            "elab_only": args.elab_only,
            "waves": args.waves,
        }
        return cls(**common_args(args), **sim_args)

    def tcl_preamble(self) -> str:
        return gen_file_header(self.tclfile, "verilator")

    def default_tcl_header(self) -> str:
        return ""

    def tcl_analysis_elaborate(self) -> str:
        return ""

    def default_tcl_body(self) -> str:
        return ""

    def tcl_footer(self) -> str:
        return ""

    def cmd(self) -> str:
        """Returns a default shell script to run Verilator."""
        self.logger.info("Generating shell script.")
        obj_dir = "obj_dir"
        executable = "simv"

        cmd = ["#!/bin/bash"]
        cmd += [gen_file_header(self.scriptfile, "verilator")]
        cmd += ["set -e"]
        cmd += self.read_env_setup_commands()
        cmd += ["echo ' '"]
        cmd += [
            "echo '--------------------------- verilator ---------------------------'"
        ]

        verilator_cmd = [
            "${VERILATOR_CMD:-verilator}",
            "--binary",
            "--timing",
            "--assert",
            "-Wno-fatal",
            "--top-module",
            self.top,
            "--Mdir",
            obj_dir,
            "-o",
            executable,
            f"-f {self.filelist}",
        ]
        if self.waves:
            verilator_cmd += ["--trace"]
        verilator_cmd += [f"-I{dir}" for dir in include_dirs(self.hdrs)]
        verilator_cmd += ["-DBR_VERILATOR"]
        verilator_cmd += [f"-D{define}" for define in self.defines]
        verilator_cmd += [f"-G{key}={value}" for key, value in self.params.items()]
        verilator_cmd += self.elab_opts
        verilator_cmd = " ".join(verilator_cmd)

        if self.elab_only:
            cmd += [verilator_cmd]
        else:
            sim_cmd = " ".join([f"./{obj_dir}/{executable}"] + self.sim_opts)
            cmd += [" && ".join([verilator_cmd, sim_cmd])]
        cmd += [""]
        return "\n".join(cmd)

    def run_cmd(self) -> Dict[str, bool]:
        """Runs a shell script and returns a dict of success criteria."""
        self.logger.info("Running shell script.")
        self.prepare_files()
        returncode, shell_output = run_shell_script(self.scriptfile, self.logger)
        write_and_dump_file(shell_output, self.logfile, logger=self.logger)
        return check_simulation_success(returncode, self.elab_only, shell_output)

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
