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

"""Main entry point for Verilog Runner."""

import argparse
import logging
import os
import sys

from cli import Elab, Lint, Sim, Fpv, add_common_args, parse_params
from plugins import discover_plugins
from util import MAIN_FILE_ABBREV, print_greeting

# Configure the root logger
root_logger = logging.getLogger()
root_logger.setLevel(logging.INFO)

# Create handler for the root logger
root_handler = logging.StreamHandler(sys.stdout)
root_formatter = logging.Formatter(
    "[" + MAIN_FILE_ABBREV + "][%(filename)s:%(lineno)-4d] %(message)s"
)
root_handler.setFormatter(root_formatter)
root_logger.addHandler(root_handler)


def main():
    print_greeting()
    logging.info("Working directory: " + os.getcwd())
    logging.info("Python binary: " + sys.executable)
    logging.info("Python version: " + sys.version)
    logging.info("Python path: " + str(sys.path))

    parser = argparse.ArgumentParser(
        description="Run a Verilog/SystemVerilog test.",
        allow_abbrev=False,
    )
    parent_parser = argparse.ArgumentParser(add_help=False)
    add_common_args(parent_parser)

    # Get plugin directories from environment variable
    logging.info(
        "Getting plugin directories from VERILOG_RUNNER_PLUGIN_PATH environment variable."
    )
    plugin_dirs_env = os.environ.get("VERILOG_RUNNER_PLUGIN_PATH", "")
    plugin_dirs = plugin_dirs_env.split(os.pathsep)

    allowed_subcommands = (Elab, Lint, Sim, Fpv)
    subcommand_name_to_class = {cls.name: cls for cls in allowed_subcommands}

    # Discover plugins and add subparsers per allowed subcommand
    subparsers = parser.add_subparsers(
        dest="subcommand", required=True, help="Subcommands"
    )
    logging.info("Discovering plugins...")
    plugins_by_subcommand = discover_plugins(plugin_dirs, allowed_subcommands)
    for subcommand, tool_plugins in plugins_by_subcommand.items():
        subcommand_parser = subparsers.add_parser(
            subcommand.name,
            parents=[parent_parser],
            help=subcommand.help,
        )
        # Add subcommand-specific (but not tool-specific) arguments
        subcommand.add_args(subcommand_parser)
        # Add the '--tool' argument with choices based on available tools offered by plugins.
        tool_choices = list(tool_plugins.keys())
        subcommand_parser.add_argument(
            "--tool",
            type=str,
            help=f"Tool to use for subcommand {subcommand.name}. Default is the first tool: {tool_choices[0]}.",
            choices=tool_choices,
            default=tool_choices[0],
        )

    logging.info("Parsing command line arguments...")
    args = parser.parse_args()

    if len(args.opt) > 0 and not args.tool:
        raise ValueError(
            "--tool must be provided when --opt flags are provided, because --opt values are tool-specific."
        )

    args.params = parse_params(parser, args.param)

    logging.info(f"Subcommand: {args.subcommand}")
    logging.info(f"Tool: {args.tool}")

    # Select the appropriate plugin class
    subcommand_class = subcommand_name_to_class.get(args.subcommand)
    tool_plugins = plugins_by_subcommand.get(subcommand_class)
    plugin_class = tool_plugins.get(args.tool)

    # Instantiate the plugin
    plugin = plugin_class.from_args(args)

    if args.dry_run:
        plugin.prepare_files()
        success = True
    else:
        success = plugin.run_test()

    exit(0 if success else 1)


if __name__ == "__main__":
    main()
