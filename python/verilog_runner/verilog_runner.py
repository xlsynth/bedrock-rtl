# SPDX-License-Identifier: Apache-2.0


"""Main entry point for Verilog Runner."""

import argparse
import logging
import os
import sys

from cli import Elab, Lint, Sim, Fpv, Chipstack, add_common_args, parse_params
from plugins import discover_plugins
from util import print_greeting, init_root_logger


def get_plugin_dirs_from_env() -> list[str]:
    logging.info(
        "Getting additional plugin directories from VERILOG_RUNNER_PLUGIN_PATH environment variable. "
        "Note that the current directory is always searched for plugins "
        "regardless of the environment variable setting."
    )
    plugin_dirs_env = os.environ.get("VERILOG_RUNNER_PLUGIN_PATH", "")
    logging.info(f"VERILOG_RUNNER_PLUGIN_PATH: {plugin_dirs_env}")
    plugin_dirs = plugin_dirs_env.split(os.pathsep)
    if plugin_dirs[0] == "":
        logging.info(
            "Stripping off empty first element from VERILOG_RUNNER_PLUGIN_PATH."
        )
        plugin_dirs = plugin_dirs[1:]
    logging.info("Adding current directory to plugin search path.")
    plugin_dirs += ["."]
    return plugin_dirs


def main():
    print_greeting()
    init_root_logger()
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

    plugin_dirs = get_plugin_dirs_from_env()

    allowed_subcommands = (Elab, Lint, Sim, Fpv, Chipstack)
    subcommand_name_to_class = {cls.name: cls for cls in allowed_subcommands}

    # Discover plugins and add subparsers per allowed subcommand
    subparsers = parser.add_subparsers(
        dest="subcommand", required=True, help="Subcommands"
    )
    logging.info("Discovering plugins...")
    plugins_by_subcommand = discover_plugins(plugin_dirs, allowed_subcommands)

    if len(plugins_by_subcommand) == 0:
        raise ValueError(
            "No plugins found! Are you sure that the VERILOG_RUNNER_PLUGIN_PATH environment variable is set correctly?"
        )

    for subcommand, tool_plugins in plugins_by_subcommand.items():
        subcommand_parser = subparsers.add_parser(
            subcommand.name,
            parents=[parent_parser],
            help=subcommand.help,
        )
        # Add subcommand-specific (but not tool-specific) arguments
        subcommand.add_args(subcommand_parser)
        for _, plugin_class in tool_plugins.items():
            plugin_class.add_args(subcommand_parser)
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
