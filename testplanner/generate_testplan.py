#!/bin/python
# SPDX-License-Identifier: Apache-2.0

"""Generate Testplanner HJSON testplan inputs from Bazel test output.

This script converts the list of tests printed by Bazel into per-testplan HJSON files
containing Testplanner testpoints. These files are consumed by Testplanner
to build the static report page.
"""

from dataclasses import dataclass
from pathlib import Path
import argparse
import json
import os

from utils import get_categories, parse_logs, TestResult


def get_tests_from_testpoint(tp: str, test_results: list[TestResult]) -> list[str]:
    """Return names of tests that belong to the given testpoint category."""

    tests = list()

    for result in test_results:
        if result.category == tp:
            tests.append(result.name)

    return tests


def create_testpoints(
    test_results: list[TestResult], tp: str, hjson_out: dict, tests_category: str
):
    """Append a Testplanner testpoint entry for one Bazel package category."""

    tp_append = {
        "name": tp,
        "desc": tp + " tests",
        "stage": tests_category,
        "tests": get_tests_from_testpoint(tp, test_results),
        "tags": [""],
    }
    hjson_out["testpoints"].append(tp_append)


def generate_testplan(input_file: Path, tests_category: str, output_dir: Path):
    """Parse Bazel test results and write Testplanner HJSON files with testpoints."""

    output_dir.mkdir(exist_ok=True)

    test_results = parse_logs(input_file)
    tps = get_categories(test_results)

    for tp in tps:
        with (output_dir / f"testplan_{tests_category}_{tp}.hjson").open("w") as fd:
            hjson_out = {"name": tp, "testpoints": []}

            create_testpoints(test_results, tp, hjson_out, tests_category)
            json.dump(hjson_out, fd, indent=4)


def parse_args():
    """Parse command-line arguments for testplan generation."""

    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", metavar="bazel_test_results", type=Path)
    parser.add_argument("tests_category")
    parser.add_argument("output_dir", default=Path("./testplans"), type=Path)
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    generate_testplan(args.input_file, args.tests_category, args.output_dir)
