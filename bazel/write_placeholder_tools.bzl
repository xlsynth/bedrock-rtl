# Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Placeholder tool code generation for Verilog/SystemVerilog lint and elaboration tests."""

_PLACEHOLDER_VERILOG_TEST_TOOL_CONTENT = '''#!/usr/bin/env python3.12

# # Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Auto-generated code: placeholder Python implementation of the verilog_test tool API."""

import argparse
from typing import Dict, List, Optional, Tuple
import os
import textwrap
import re
import subprocess
import tabulate

THIS_FILE = os.path.basename(__file__)
PASS_ART = f"""
######   #######   ######  ######
##  ##   ##   ##   ##      ##
######   #######   ######  ######
##       ##   ##       ##      ##
##       ##   ##   ######  ######
"""
FAIL_ART = f"""
######   #######  ######   ##
##       ##   ##    ##     ##
######   #######    ##     ##
##       ##   ##    ##     ##
##       ##   ##  ######   #######
"""


def wrap_text(text, width=60):
    return "\\n".join(textwrap.wrap(text, width))


def dump_file_to_stdout(filename: str) -> None:
    full_path = os.path.realpath(filename)
    print(
        textwrap.dedent(
            f"""

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    {THIS_FILE}: Dump of {full_path}
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    """
        )
    )
    with open(filename, "r", errors="replace") as file:
        print(file.read())


def print_summary(success: bool, step_success: Dict[str, bool], report_table) -> None:
    step_success_text = "\\n".join(
        f"{k}: {'OK' if v else 'FAIL'}" for k, v in step_success.items()
    )
    print(
        f"""

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
{THIS_FILE}: Test summary
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

{step_success_text}

{report_table if not success else ""}

{PASS_ART if success else FAIL_ART}
{"PASS" if success else "FAIL"}
    """
    )


def check_each_filename_suffix(filenames: List[str], suffices: List[str]) -> None:
    """Raises ValueError if there is any filename in the list that doesn't end with any of the expected suffices."""
    for filename in filenames:
        match = False
        for suffix in suffices:
            if filename.endswith(suffix):
                match = True
                break
        if not match:
            raise ValueError(
                f"Expected filename to end with any of {suffices}: {filename}"
            )


def parse_params(
    parser: argparse.ArgumentParser, params: Optional[List[str]]
) -> Dict[str, str]:
    """Parses parameters into a dict; raises an error if any of the parameters are not in the expected KEY=VALUE format."""
    params_dict = {}
    if params:
        for item in params:
            if "=" in item:
                key, value = item.split("=", 1)
                params_dict[key] = value
            else:
                parser.error(
                    f"Invalid format for --param '{item}'. Expected KEY=VALUE."
                )
    return params_dict

def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--top",
        type=str,
        required=True,
        help="Top module",
    )
    parser.add_argument(
        "--hdr",
        type=argparse.FileType("r"),
        action="append",
        default=[],
        help="Verilog header (.vh) or SystemVerilog header (.svh) to include. "
        "Can be specified multiple times.",
    )
    parser.add_argument(
        "--define",
        type=str,
        action="append",
        default=[],
        help="Verilog/SystemVerilog preprocessor define to use in compilation. Can be specified multiple times.",
    )
    parser.add_argument(
        "--param",
        action="append",
        metavar="KEY=VALUE",
        default=[],
        help="Verilog/SystemVerilog module parameter key-value pair for the top module. Can be specified multiple times.",
    )
    parser.add_argument(
        "srcs",
        type=argparse.FileType("r"),
        nargs="+",
        help="One or more Verilog (.h) or SystemVerilog (.sv) source files",
    )


def add_sim_fpv_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--opt",
        type=str,
        action="append",
        default=[],
        help="Tool options. Can be specified multiple times.",
    )
    parser.add_argument(
        "--elab_only",
        action="store_true",
        help="Only run elaboration.",
    )

def add_sim_args(parser: argparse.ArgumentParser) -> None:
    add_sim_fpv_args(parser)
    parser.add_argument(
        "--tool",
        type=str,
        help="Simulator tool to use.",
        required=True,
    )
    parser.add_argument(
        "--uvm",
        action="store_true",
        help="Run UVM test.",
    )
    parser.add_argument(
        "--seed",
        type=int,
        help="Seed to use in simulation. If not provided, a random value will be chosen.",
    )
    parser.add_argument(
        "--waves",
        action="store_true",
        help="Enable waveform dumping.",
    )

def add_fpv_args(parser: argparse.ArgumentParser) -> None:
    add_sim_fpv_args(parser)
    parser.add_argument(
        "--tool",
        type=str,
        help="Formal tool to use.",
        required=True,
    )

def main():
    parser = argparse.ArgumentParser(
        description="Run a Verilog/SystemVerilog test.",
        allow_abbrev=False,
    )
    parent_parser = argparse.ArgumentParser(add_help=False)
    add_common_args(parent_parser)
    subparsers = parser.add_subparsers(
        dest="subcommand", required=True, help="Subcommands"
    )
    elab_subparser = subparsers.add_parser(
        "elab", parents=[parent_parser], help="Elaborate a Verilog/SystemVerilog design"
    )
    lint_subparser = subparsers.add_parser(
        "lint", parents=[parent_parser], help="Lint a Verilog/SystemVerilog design"
    )
    sim_subparser = subparsers.add_parser(
        "sim", parents=[parent_parser], help="Simulate a Verilog/SystemVerilog design"
    )
    add_sim_args(sim_subparser)
    fpv_subparser = subparsers.add_parser(
        "fpv", parents=[parent_parser], help="fpvulate a Verilog/SystemVerilog design"
    )
    add_fpv_args(fpv_subparser)

    args = parser.parse_args()

    hdrs = [hdr.name for hdr in args.hdr]
    srcs = [src.name for src in args.srcs]
    defines = args.define
    params = parse_params(parser, args.param)

    check_each_filename_suffix(hdrs, [".vh", ".svh"])
    check_each_filename_suffix(srcs, [".v", ".sv"])

    success = False
    if args.subcommand == "elab":
        success = True
        print("NOT IMPLEMENTED: Elab test vacuously passes.")
    elif args.subcommand == "lint":
        success = True
        print("NOT IMPLEMENTED: Lint test vacuously passes.")
    elif args.subcommand == "sim":
        success = True
        print("NOT IMPLEMENTED: Sim test vacuously passes.")
    elif args.subcommand == "fpv":
        success = True
        print("NOT IMPLEMENTED: Formal test vacuously passes.")
    else:
        raise ValueError(f"Invalid subcommand: {args.subcommand}")

    exit(0 if success else 1)


if __name__ == "__main__":
    main()
'''

def write_placeholder_verilog_test_tool(ctx, filename):
    """Writes a placeholder Python implementation of the verilog_test tool API."""
    file = ctx.actions.declare_file(filename)
    ctx.actions.write(
        output = file,
        content = _PLACEHOLDER_VERILOG_TEST_TOOL_CONTENT,
        is_executable = True,
    )
    return file
