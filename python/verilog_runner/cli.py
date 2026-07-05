# SPDX-License-Identifier: Apache-2.0


"""Verilog Runner CLI."""

from abc import ABC, abstractmethod
import argparse
import os
import re
from typing import List, Dict
from util import check_filename_extension


def verilog_file(filename: str) -> str:
    # .vp and .svp are encrypted files.
    return check_filename_extension(filename, (".v", ".sv", ".vp", ".svp"), error=False)


def verilog_header_file(filename: str) -> str:
    # Some vendor libraries include .h, .v, and .sv files rather than
    # following the .vh/.svh convention.
    return check_filename_extension(
        filename, (".vh", ".svh", ".h", ".v", ".sv"), error=False
    )


def tcl_file(filename: str) -> str:
    return check_filename_extension(filename, (".tcl"))


def sh_file(filename: str) -> str:
    return check_filename_extension(filename, (".sh"))


def log_file(filename: str) -> str:
    return check_filename_extension(filename, (".log"))


def filelist_file(filename: str) -> str:
    return check_filename_extension(filename, (".f"))


def liberty_file(filename: str) -> str:
    filename = check_filename_extension(filename, (".lib", ".lib.gz"))
    path = os.path.normpath(filename)
    if os.path.isabs(path) or path == ".." or path.startswith("../"):
        raise argparse.ArgumentTypeError(
            f"Liberty path '{filename}' must be relative to --liberty_root_env."
        )
    if not re.fullmatch(r"[A-Za-z0-9_./+-]+", path):
        raise argparse.ArgumentTypeError(
            f"Liberty path '{filename}' contains unsupported characters."
        )
    return path


def environment_variable_name(value: str) -> str:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value):
        raise argparse.ArgumentTypeError(
            f"'{value}' is not a valid environment-variable name."
        )
    return value


def liberty_sha256(value: str) -> tuple[str, str]:
    if "=" not in value:
        raise argparse.ArgumentTypeError(
            f"Invalid Liberty checksum '{value}'. Expected PATH=SHA256."
        )
    path, digest = value.split("=", 1)
    path = liberty_file(path)
    if not re.fullmatch(r"[0-9a-fA-F]{64}", digest):
        raise argparse.ArgumentTypeError(
            f"Invalid SHA-256 digest for Liberty path '{path}'."
        )
    return path, digest.lower()


def add_common_args(parser: argparse.ArgumentParser) -> None:
    """Common arguments for all subcommands and plugins."""
    parser.add_argument(
        "--top",
        type=str,
        help="Top module. May be omitted for compile-only elaboration.",
    )
    parser.add_argument(
        "--hdr",
        type=verilog_header_file,
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
        "--dry-run",
        action="store_true",
        help="Prepare the test command, including writing necessary files, but don't actually run the EDA tool command.",
    )
    parser.add_argument(
        "--opt",
        type=str,
        action="append",
        default=[],
        # TODO(mgottscho): Move tool-specific option flags out of the common CLI
        # surface once each subcommand has its own option model.
        help="Tool-specific options to pass directly to the tool. Can be specified multiple times. "
        "If provided, then --tool must be provided explicitly.",
    )
    parser.add_argument(
        "--tcl",
        type=tcl_file,
        help="Tcl script file to write commands to. The generated tcl script consists of three parts: header, body, and footer."
        "The tcl header is unconditionally followed by analysis and elaborate commands, then the tcl body."
        "The tcl body is unconditionally followed by the tcl footer."
        "By default, header, body, and footer are all auto-generated, but the header and body can be overridden "
        "by --custom_tcl_header and --custom_tcl_body, respectively.",
        required=True,
    )
    parser.add_argument(
        "--custom_tcl_header",
        type=tcl_file,
        help="Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script."
        "The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.",
    )
    parser.add_argument(
        "--custom_tcl_body",
        type=tcl_file,
        help="Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script."
        "The tcl body (custom or not) is unconditionally followed by the tcl footer.",
    )
    parser.add_argument(
        "--script",
        type=sh_file,
        help="Shell script file to write commands to.",
        required=True,
    )
    parser.add_argument(
        "--log",
        type=log_file,
        help="Log file to write tool stdout/stderr to.",
        required=True,
    )
    parser.add_argument(
        "--filelist",
        type=filelist_file,
        help="Filelist file to write srcs list to.",
        required=True,
    )
    parser.add_argument(
        "srcs",
        type=verilog_file,
        nargs="+",
        help="One or more Verilog (.h) or SystemVerilog (.sv) source files",
    )


def parse_params(parser: argparse.ArgumentParser, params: List[str]) -> Dict[str, str]:
    """Parses Verilog parameter args into a dict; raises an error if any of the parameters are not in the expected KEY=VALUE format."""
    params_dict = {}
    for item in params:
        if "=" in item:
            key, value = item.split("=", 1)
            params_dict[key] = value
        else:
            parser.error(f"Invalid format for --param '{item}'. Expected KEY=VALUE.")
    return params_dict


def validate_top(parser: argparse.ArgumentParser, args: argparse.Namespace) -> None:
    """Validates that a top is present unless the command is compile-only elaboration."""
    if not args.top and not (
        args.subcommand == Elab.name and getattr(args, "compile_only", False)
    ):
        parser.error("--top is required unless --compile_only is used with elab")


def common_args(args: argparse.Namespace):
    def get_env_setup_command_file_from_env() -> str:
        import logging
        import os

        logging.info("Reading VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP environment variable.")
        var = os.environ.get("VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP", "")
        if var == "":
            logging.info(
                "VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP environment variable is not set."
            )
        else:
            logging.info(
                f"VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP environment variable is set to '{var}'."
            )
        return var

    common = {
        "hdrs": args.hdr,
        "defines": args.define,
        "params": args.params,
        # TODO(mgottscho): Stop threading `opts` through common_args once the
        # CLI no longer models tool-specific options as a common concept.
        "opts": args.opt,
        "srcs": args.srcs,
        "top": args.top,
        "tclfile": args.tcl,
        "scriptfile": args.script,
        "logfile": args.log,
        "filelist": args.filelist,
        "tclfile_custom_header": args.custom_tcl_header,
        "tclfile_custom_body": args.custom_tcl_body,
        # Use an environment variable instead of CLI arg because Bazel doesn't know the value at
        # analysis time (when the verilog runner command is constructed).
        "env_setup_commands": get_env_setup_command_file_from_env(),
    }
    if getattr(args, "subcommand", None) == "sim":
        if len(args.opt) > 0 and args.tool != "vcs":
            raise ValueError(
                "--opt is a legacy VCS-only simulation option. Use --elab_opt "
                "for compile/elaboration options or --sim_opt for runtime options."
            )
        common["elab_opts"] = getattr(args, "elab_opt", [])
        common["sim_opts"] = getattr(args, "sim_opt", [])
    elif getattr(args, "subcommand", None) == "synth":
        common["liberties"] = getattr(args, "liberty", [])
        common["sequential_liberty"] = getattr(args, "sequential_liberty", None)
        common["liberty_root_env"] = getattr(args, "liberty_root_env", None)
        common["liberty_sha256"] = dict(getattr(args, "liberty_sha256", []))
        common["synth_profile"] = getattr(args, "synth_profile", "generic")
        common["clock_period_ps"] = getattr(args, "clock_period_ps", None)
        common["input_driver_cell"] = getattr(args, "input_driver_cell", None)
        common["output_load_ff"] = getattr(args, "output_load_ff", None)
    return common


class Subcommand(ABC):
    """Abstract base class for subcommands."""

    name: str
    help: str

    def __init__(self, name: str, help: str) -> None:
        self.name = name
        self.help = help

    @abstractmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        pass


class Elab(Subcommand):
    name = "elab"
    help = "Static elaboration test"

    @staticmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--compile_only",
            action="store_true",
            help="Compile and type-check sources without elaborating a top-level module.",
        )


class Lint(Subcommand):
    name = "lint"
    help = "Lint test"

    @staticmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--policy",
            type=str,
            help="Lint policy to use. If not provided, lint tool will use a default (may depend on tool-specific environment variables).",
            required=False,
        )


class Sim(Subcommand):
    name = "sim"
    help = "Simulation test"

    @staticmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--elab_only",
            action="store_true",
            help="Only run elaboration.",
        )
        parser.add_argument(
            "--elab_opt",
            type=str,
            action="append",
            default=[],
            help="Tool-specific compile/elaboration options.",
        )
        parser.add_argument(
            "--sim_opt",
            type=str,
            action="append",
            default=[],
            help="Tool-specific simulation runtime options, such as simulator plusargs.",
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
        parser.add_argument(
            "--coverage",
            type=str,
            default=None,
            help="Path where coverage data will be saved, if None the coverage is not enabled",
        )


class Fpv(Subcommand):
    name = "fpv"
    help = "Formal property verification test"

    @staticmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--elab_only",
            action="store_true",
            help="Only run elaboration.",
        )
        parser.add_argument(
            "--gui",
            action="store_true",
            help="Run with GUI",
        )
        parser.add_argument(
            "--elab_opt",
            type=str,
            action="append",
            default=[],
            help="elab options",
        )
        parser.add_argument(
            "--analysis_opt",
            type=str,
            action="append",
            default=[],
            help="analysis options",
        )
        parser.add_argument(
            "--conn",
            action="store_true",
            help="Run in connectivity mode",
        )


class Synth(Subcommand):
    name = "synth"
    help = "Logic synthesis"

    @staticmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--liberty",
            type=liberty_file,
            action="append",
            default=[],
            help="Liberty path relative to --liberty_root_env. May be repeated.",
        )
        parser.add_argument(
            "--sequential_liberty",
            type=liberty_file,
            help="Liberty path used for sequential-cell mapping when libraries are split.",
        )
        parser.add_argument(
            "--liberty_root_env",
            type=environment_variable_name,
            help="Environment variable containing the system-provided Liberty root.",
        )
        parser.add_argument(
            "--liberty_sha256",
            type=liberty_sha256,
            action="append",
            default=[],
            metavar="PATH=SHA256",
            help="Expected checksum for one Liberty path. May be repeated.",
        )
        parser.add_argument(
            "--synth_profile",
            default="generic",
            help="Stable synthesis profile recorded in generated reports.",
        )
        parser.add_argument(
            "--clock_period_ps",
            type=int,
            help="Optional target clock period in picoseconds for technology mapping.",
        )
        parser.add_argument(
            "--input_driver_cell",
            help="Optional Liberty cell assumed to drive each primary input.",
        )
        parser.add_argument(
            "--output_load_ff",
            type=float,
            help="Optional capacitive load in femtofarads on each primary output.",
        )
