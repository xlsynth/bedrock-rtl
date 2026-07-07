# SPDX-License-Identifier: Apache-2.0

from dataclasses import dataclass
import re


@dataclass
class TestResult:
    category: str
    postfix: str
    name: str
    result: str
    time: str


def get_categories(test_results: list[TestResult]) -> set[str]:
    """Return all unique testplan categories found in parsed Bazel results."""

    return set(result.category for result in test_results)


def parse_logs(input_file: str) -> list[TestResult]:
    """Parse log files and creates list of test results."""
    # Pattern for matching Bazel test logs like:
    # "//amba/sim:br_amba_apb_timing_slice_sim_test_tools_suite_verilator_aw12_sim_test PASSED in 8.2s"
    # resulting with category="amba",
    # name="br_amba_apb_timing_slice_sim_test_tools_suite_verilator_aw12_sim_test"
    # posetfix="sim", results="PASSED" and time="8.2"
    pattern = re.compile(
        r"""\s*//(?P<category>[^/]+?)(?:/(?P<postfix>[^:]+?))?:(?P<name>.*?)
                             \s+(?P<result>.*?)\s+in\s+(?P<time>.*?)s""",
        re.VERBOSE,
    )
    test_results = list()

    with open(input_file) as f:
        for line in f:
            match = pattern.match(line)
            if match == None:
                print(f"Regex couldn't match the expression on line: {line.rstrip()}")
                raise SystemExit(1)

            result = TestResult(
                category=match.group("category"),
                postfix=match.group("postfix"),
                name=match.group("name"),
                result=match.group("result"),
                time=match.group("time"),
            )
            test_results.append(result)
    return test_results
