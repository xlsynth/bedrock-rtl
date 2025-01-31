# Copyright 2024-2025 The Bedrock-RTL Authors
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

"""Util functions for Verilog Runner and its plugins."""

import argparse
import math
import logging
import os
import random
import subprocess
import sys
import textwrap
from typing import Dict, Tuple, List


MAIN_FILE_ABBREV = "vr"
MAIN_FILE = "verilog_runner.py"
PASS_ART = f"""
######   #######   ######  ######
##  ##   ##   ##   ##      ##
######   #######   ######  #####
##       ##   ##       ##      ##
##       ##   ##   ######  ######"""
FAIL_ART = f"""
######   #######  ######   ##
##       ##   ##    ##     ##
######   #######    ##     ##
##       ##   ##    ##     ##
##       ##   ##  ######   #######"""
SEPARATOR = "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"


class MaxLevelFilter(logging.Filter):
    def __init__(self, max_level):
        super().__init__()
        self.max_level = max_level

    def filter(self, record):
        # Allow only records with a level number below max_level
        return record.levelno < self.max_level


def get_class_logger(subcommand: str, tool: str) -> logging.LoggerAdapter:
    logger = logging.getLogger(subcommand)
    logger.propagate = False
    logger.setLevel(logging.INFO)

    # Formatters
    general_formatter = logging.Formatter(
        f"[{MAIN_FILE_ABBREV}][%(name)s][%(tool)s][%(filename)s:%(lineno)-4d] %(message)s"
    )
    warning_error_formatter = logging.Formatter(
        f"[{MAIN_FILE_ABBREV}][%(name)s][%(tool)s][%(filename)s:%(lineno)-4d] !! %(levelname)s !! %(message)s"
    )

    # Handler for INFO and below to stdout
    stdout_handler = logging.StreamHandler(sys.stdout)
    stdout_handler.setLevel(logging.INFO)
    stdout_handler.addFilter(
        MaxLevelFilter(logging.WARNING)
    )  # Exclude WARNING and above
    stdout_handler.setFormatter(general_formatter)

    # Handler for WARNING and above to stderr
    stderr_handler = logging.StreamHandler(sys.stderr)
    stderr_handler.setLevel(logging.WARNING)
    stderr_handler.setFormatter(warning_error_formatter)

    logger.addHandler(stdout_handler)
    logger.addHandler(stderr_handler)

    adapter = logging.LoggerAdapter(logger, {"tool": tool})
    return adapter


def init_root_logger():
    # Configure the root logger
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.INFO)

    # Formatter for regular messages
    general_formatter = logging.Formatter(
        f"[{MAIN_FILE_ABBREV}][%(filename)s:%(lineno)-4d] %(message)s"
    )

    # Formatter for warnings/errors
    warning_error_formatter = logging.Formatter(
        f"[{MAIN_FILE_ABBREV}][%(filename)s:%(lineno)-4d] !! %(levelname)s !! %(message)s"
    )

    # Handler for info-level messages to stdout
    stdout_handler = logging.StreamHandler(sys.stdout)
    stdout_handler.setLevel(logging.INFO)
    stdout_handler.addFilter(
        MaxLevelFilter(logging.WARNING)
    )  # Exclude WARNING and above
    stdout_handler.setFormatter(general_formatter)

    # Handler for warnings and errors to stderr
    stderr_handler = logging.StreamHandler(sys.stderr)
    stderr_handler.setLevel(logging.WARNING)  # handles WARNING and above
    stderr_handler.setFormatter(warning_error_formatter)

    # Add both handlers to the root logger
    root_logger.addHandler(stdout_handler)
    root_logger.addHandler(stderr_handler)


def wrap_text(text, width=60):
    """Wraps text to a specified width."""
    return "\n".join(textwrap.wrap(text, width))


def dump_file(filename: str, logger: logging.Logger) -> None:
    """Reads the contents of a file and logs it clearly by attributing filename and line number."""
    logger.info(f"Dumping {filename}")
    with open(filename, "r", errors="replace") as file:
        content = file.readlines()
        num_lines = len(content)
        line_num_width = math.ceil(math.log10(num_lines))
        file_suffix = os.path.splitext(filename)[1]
        pad = " "
        pad_width = 16 - line_num_width - len(file_suffix) - 3
        for line_number, line in enumerate(content, start=1):
            line = line.rstrip("\n")
            logger.info(
                f"{pad:<{pad_width}s}({file_suffix}) {line_number:<{line_num_width}d}:    {line}"
            )


def print_greeting() -> None:
    print(f"{SEPARATOR} {MAIN_FILE} ({MAIN_FILE_ABBREV}) {SEPARATOR}")


def print_summary(
    success: bool,
    step_success: Dict[str, bool],
    report_table: str,
    logger: logging.Logger,
) -> None:
    """Logs a summary of the run."""
    step_success_text = "\n".join(
        f"{k}: {'OK' if v else 'FAIL'}" for k, v in step_success.items()
    )
    summary_text = "\n\n".join(
        [
            step_success_text,
            report_table if not success else "",
            PASS_ART if success else FAIL_ART,
            "PASS" if success else "FAIL",
        ]
    )
    logger.info(f"Summary:\n{SEPARATOR}\n{summary_text}\n{SEPARATOR}\n")


def check_filename_extension(
    filename: str,
    allowed_extensions: Tuple[str],
    logger: logging.Logger = None,
    error: bool = True,
) -> str:
    """Checks if a filename has one of the allowed extensions and returns it as-is."""
    if not filename.endswith(allowed_extensions):
        if error:
            raise argparse.ArgumentTypeError(
                f"File '{filename}' must have one of the extensions: {allowed_extensions}"
            )
        else:
            if logger:
                logger.warning(
                    f"File '{filename}' has an atypical extension. Expected one of: {allowed_extensions}"
                )
            else:
                logging.warning(
                    f"File '{filename}' has an atypical extension. Expected one of: {allowed_extensions}"
                )
    return filename


def gen_file_header(file: str, tool: str) -> str:
    """Returns a header string for a generated file."""
    return "\n".join(
        [
            f"# {file}",
            f"# Auto-generated by {MAIN_FILE} for use with {tool}",
        ]
    )


def include_dirs(hdrs: List[str]) -> List[str]:
    """Returns a list of unique directories containing the headers."""
    retval = set()
    for hdr in hdrs:
        base_dir = os.path.dirname(hdr)
        retval.add(base_dir)
    return list(retval)


def generate_random_seed() -> int:
    """Generates a random seed."""
    return random.randint(1, 2**32 - 1)


def to_filelist(srcs: List[str]) -> str:
    """Returns a filelist string representation of a list of sources."""
    return "\n".join(srcs) + "\n"


def write_and_dump_file(content: str, filename: str, logger: logging.Logger) -> None:
    """Writes a string to a file and then dumps its contents to stdout."""
    logger.info(f"Writing {filename}")
    with open(filename, "w") as file:
        file.write(textwrap.dedent(content))
    dump_file(filename=filename, logger=logger)


def run_shell_script(script: str, logger: logging.Logger) -> Tuple[int, str]:
    """Runs a shell script and returns a tuple of its return code and its concatenated stdout+stderr."""
    logger.info(f"Running script: {script}")
    with open(script, "r") as file:
        cmd = file.read()
    result = subprocess.run(
        cmd,
        shell=True,
        executable="/bin/bash",
        capture_output=True,
        text=True,
        errors="replace",
    )
    shell_output = "\n".join([result.stdout, result.stderr])
    return result.returncode, shell_output


def check_simulation_success(
    return_code: int, elab_only: bool, stdout: str
) -> Dict[str, bool]:
    """Returns a dict of simulation success criteria."""
    step_success = {f"Return code {return_code}": return_code == 0}
    if not elab_only:
        step_success["'TEST PASSED' in output"] = "TEST PASSED" in stdout
    return step_success
