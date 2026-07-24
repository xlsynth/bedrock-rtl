#!/bin/python

from dataclasses import dataclass

import re
import os
import json
import sys


@dataclass
class TestResult:
    category: str
    name: str
    result: str
    time: str


def get_tests_from_testpoint(tp, test_results):
    tests = list()

    for result in test_results:
        if result.category == tp:
            tests.append(result.name)

    return tests


def create_testpoints(test_results, tp, hjson_out, tests_category):
    tp_append = {
        "name": tp,
        "desc": tp + " tests",
        "stage": tests_category,
        "tests": get_tests_from_testpoint(tp, test_results),
        "tags": [""],
    }
    hjson_out["testpoints"].append(tp_append)


def get_testpoints(test_results):
    tp = set()

    for result in test_results:
        tp.add(result.category)

    return tp


def generate_testplan(input_file, tests_category):
    if not os.path.exists("./testplans"):
        os.makedirs("./testplans")

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
                sys.exit(-1)

            result = TestResult(
                category=match.group("category"),
                name=match.group("name"),
                result=match.group("result"),
                time=match.group("time"),
            )
            test_results.append(result)

    tps = get_testpoints(test_results)

    for tp in tps:
        output_file = open(f"testplans/testplan_{tests_category}_{tp}.hjson", "w")
        hjson_out = {"name": tp, "testpoints": []}

        create_testpoints(test_results, tp, hjson_out, tests_category)
        json.dump(hjson_out, output_file, indent=4)
        output_file.close()


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage {sys.argv[0]} <bazel_test_results> <tests_category>")
        sys.exit(-1)

    input_file = sys.argv[1]
    tests_category = sys.argv[2]

    generate_testplan(input_file, tests_category)
