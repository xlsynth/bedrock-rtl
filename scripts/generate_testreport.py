#!/bin/python

from dataclasses import dataclass

import re
import os
import json
import sys


@dataclass
class TestResult:
    category: str
    postfix: str
    name: str
    result: str
    time: str


def get_testplans(test_results):
    tp = set()

    for result in test_results:
        tp.add(result.category)

    return tp


def create_testresult_path(test_result):
    path = test_result.category + "/"

    if test_result.postfix:
        path += test_result.postfix + "/"

    path += test_result.name + "/"
    path += "test.log"

    return path


def get_simulated_time(test_result, testlogs_dir):
    testlog = f"{testlogs_dir}/{create_testresult_path(test_result)}"

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


def create_test_entry(test_result, testlogs_dir):
    passed = 1 if test_result.result == "PASSED" else 0
    simulated_time = get_simulated_time(test_result, testlogs_dir)
    return {
        "name": test_result.name,
        "passing": passed,
        "total": 1,
        "job_runtime": float(test_result.time),
        "simulated_time": simulated_time,
    }


def generate_testreport(input_file, timestamp, testlogs_dir, tests_category):
    if not os.path.exists("./testreports"):
        os.makedirs("./testreports")

    pattern = re.compile(
        r"""\s*//(?P<category>[^/]+?)(?:/(?P<postfix>[^:]+?))?:(?P<name>.*?)
        (?:\s+\(cached\))?\s+(?P<result>.*?)\s+in\s+(?P<time>.*?)s""",
        re.VERBOSE,
    )
    test_results = list()

    with open(input_file) as f:
        for line in f:
            match = pattern.match(line)
            if match == None:
                print("Regex couldn't match the expression on line: " + line, end="")
                sys.exit(-1)

            result = TestResult(
                category=match.group("category"),
                postfix=match.group("postfix"),
                name=match.group("name"),
                result=match.group("result"),
                time=match.group("time"),
            )
            test_results.append(result)

    tps = get_testplans(test_results)

    for tp in tps:
        hjson_out = {"timestamp": timestamp, "test_results": []}
        output_file = open(f"./testreports/testreport_{tests_category}_{tp}.hjson", "w")

        for result in test_results:
            if tp == result.category:
                hjson_out["test_results"].append(
                    create_test_entry(result, testlogs_dir)
                )

        json.dump(hjson_out, output_file, indent=4)
        output_file.close()


if __name__ == "__main__":
    if len(sys.argv) != 5:
        print(
            "Usage "
            + sys.argv[0]
            + " <bazel_test_results> <tests_timestamp> <testlogs_dir> <tests_category>"
        )
        sys.exit(-1)

    input_file = sys.argv[1]
    timestamp = sys.argv[2]
    testlogs_dir = sys.argv[3]
    tests_category = sys.argv[4]

    generate_testreport(input_file, timestamp, testlogs_dir, tests_category)
