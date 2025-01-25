# Copyright 2025 The Bedrock-RTL Authors
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

"""Logging utilities for Verilog Runner."""
import logging
import sys

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
