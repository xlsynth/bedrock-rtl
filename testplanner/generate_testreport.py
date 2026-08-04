#!/bin/python
# SPDX-License-Identifier: Apache-2.0

"""Generate Testplanner HJSON result inputs from Bazel test output.

This script converts Bazel test results and simulation logs
into per-testplan HJSON result files containing timestamps, pass counts, runtimes,
and simulated times. Testplanner uses these result files together
with the generated testplans to annotate tests and build the static report page.
"""

from dataclasses import dataclass
from pathlib import Path
import argparse
import json
import os
import re

from utils import get_categories, parse_logs, TestResult


def create_testresult_path(test_result: TestResult) -> Path:
    """Build the Bazel test.log path for a parsed test result."""

    path = Path(test_result.category)

    if test_result.postfix:
        path /= test_result.postfix

    path /= test_result.name
    path /= "test.log"

    return path


def get_simulated_time(test_result: TestResult, testlogs_dir: Path) -> str:
    """Extract the simulation finish time from a test's Bazel log."""

    testlog = testlogs_dir / create_testresult_path(test_result)

    # Extract simulation time from lines like:
    # - Verilator: $finish at 1us; walltime 0.000 s; speed 6.873 ms/s
    pattern = re.compile(
        r""".*?\$finish\s+at\s+(?P<sim_time>[\d.]+[a-zuns]+)\s*;""",
        re.VERBOSE | re.IGNORECASE,
    )

    with open(testlog) as f:
        for line in f:
            match = pattern.match(line)
            if match:
                return match.group("sim_time")

    return "N.A."


def create_test_entry(test_result, testlogs_dir) -> dict:
    """Convert one parsed Bazel result into a Testplanner result entry."""

    passed = 1 if test_result.result == "PASSED" else 0
    simulated_time = get_simulated_time(test_result, testlogs_dir)
    return {
        "name": test_result.name,
        "passing": passed,
        "total": 1,
        "job_runtime": float(test_result.time),
        "simulated_time": simulated_time,
    }


def generate_testreport(
    input_file: Path,
    timestamp: str,
    testlogs_dir: Path,
    tests_category: str,
    output_dir: Path,
):
    """Parse Bazel results and write Testplanner test report HJSON files."""

    output_dir.mkdir(exist_ok=True)

    test_results = parse_logs(input_file)
    tps = get_categories(test_results)

    for tp in tps:
        hjson_out = {"timestamp": timestamp, "test_results": []}
        with (output_dir / f"testreport_{tests_category}_{tp}.hjson").open("w") as fd:
            for result in test_results:
                if tp != result.category:
                    continue
                hjson_out["test_results"].append(
                    create_test_entry(result, testlogs_dir)
                )

            json.dump(hjson_out, fd, indent=4)


def parse_args():
    """Parse command-line arguments for test report generation."""

    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", metavar="bazel_test_results", type=Path)
    parser.add_argument("timestamp", metavar="tests_timestamp")
    parser.add_argument("testlogs_dir", type=Path)
    parser.add_argument("tests_category")
    parser.add_argument("output_dir", default=Path("./testreports"), type=Path)
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    generate_testreport(
        args.input_file,
        args.timestamp,
        args.testlogs_dir,
        args.tests_category,
        args.output_dir,
    )
