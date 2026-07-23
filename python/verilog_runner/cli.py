# SPDX-License-Identifier: Apache-2.0


"""Verilog Runner CLI."""

from abc import ABC, abstractmethod
import argparse
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
    return check_filename_extension(filename, (".tcl", ".sby"))


def tcl_fragment_file(filename: str) -> str:
    return check_filename_extension(filename, (".tcl"))


def sh_file(filename: str) -> str:
    return check_filename_extension(filename, (".sh"))


def log_file(filename: str) -> str:
    return check_filename_extension(filename, (".log"))


def filelist_file(filename: str) -> str:
    return check_filename_extension(filename, (".f"))


def liberty_file(filename: str) -> str:
    return check_filename_extension(filename, (".lib"))


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
        "--data",
        type=str,
        action="append",
        default=[],
        help="Auxiliary data file needed by the design. Can be specified multiple times.",
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
        help="Legacy plugin-specific options. Their meaning is defined by the selected plugin; "
        "for SBY they are yosys-slang analysis options. Can be specified multiple times.",
    )
    parser.add_argument(
        "--tcl",
        type=tcl_file,
        help="Tool-specific control file to write (.tcl or .sby). The generated control file consists of "
        "a header, analysis and elaboration commands, a body, and a footer. "
        "By default all parts are auto-generated, but the header and body can be overridden "
        "by the corresponding --custom_control_* arguments. Tcl-based tools may use the "
        "equivalent --custom_tcl_* aliases.",
        required=True,
    )
    parser.add_argument(
        "--custom_control_header",
        type=tcl_file,
        help="Tool-neutral control fragment inserted before analysis and elaboration commands.",
    )
    parser.add_argument(
        "--custom_control_body",
        type=tcl_file,
        help="Tool-neutral control fragment replacing the default body.",
    )
    parser.add_argument(
        "--custom_tcl_header",
        type=tcl_fragment_file,
        help="Tcl-specific alias for --custom_control_header.",
    )
    parser.add_argument(
        "--custom_tcl_body",
        type=tcl_fragment_file,
        help="Tcl-specific alias for --custom_control_body.",
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

    def resolve_custom_control_fragment(fragment: str):
        control_arg = getattr(args, "custom_control_" + fragment, None)
        tcl_arg = getattr(args, "custom_tcl_" + fragment, None)
        if control_arg and tcl_arg:
            raise ValueError(
                "--custom_control_{} and --custom_tcl_{} are aliases; specify only one".format(
                    fragment, fragment
                )
            )
        if tcl_arg and args.tool == "sby":
            raise ValueError(
                "SBY control fragments must use --custom_control_{} rather than "
                "the Tcl-specific --custom_tcl_{} alias".format(fragment, fragment)
            )
        return control_arg or tcl_arg

    custom_control_header = resolve_custom_control_fragment("header")
    custom_control_body = resolve_custom_control_fragment("body")

    common = {
        "hdrs": args.hdr,
        "data": args.data,
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
        # TODO(mgottscho): Rename the internal tclfile_* plugin API to
        # control_file_* in a versioned plugin API migration. The public
        # tool-neutral and Tcl-specific aliases normalize here to preserve
        # compatibility with existing plugins.
        "tclfile_custom_header": custom_control_header,
        "tclfile_custom_body": custom_control_body,
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
        common["liberty"] = getattr(args, "liberty", None)
        common["clock_period_ps"] = getattr(args, "clock_period_ps", None)
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
            help="Request GUI mode. Not all FPV plugins support this mode.",
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
            help="Request connectivity mode. Not all FPV plugins support this mode.",
        )


class Synth(Subcommand):
    name = "synth"
    help = "Logic synthesis"

    @staticmethod
    def add_args(parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--liberty",
            type=liberty_file,
            help="Optional Liberty standard-cell library for technology mapping.",
        )
        parser.add_argument(
            "--clock_period_ps",
            type=int,
            help="Optional target clock period in picoseconds for technology mapping.",
        )
