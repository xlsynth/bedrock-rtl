# SPDX-License-Identifier: Apache-2.0

"""Deterministically partitions and aggregates public Bazel CI test targets."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Iterable


SCHEMA_VERSION = 1
PASSING_TESTS_RE = re.compile(r"(\d+) tests? pass(?:es)?")
SUITES = ("python", "stardoc", "slang", "verilator", "coverage")
BUILD_SUITES = frozenset({"coverage"})


def canonicalize_labels(lines: Iterable[str]) -> list[str]:
    """Returns sorted, unique Bazel labels after validating their shape."""

    labels = []
    for line in lines:
        label = line.strip()
        if not label:
            continue
        if not label.startswith("//") or any(
            character.isspace() for character in label
        ):
            raise ValueError(f"invalid Bazel label: {label!r}")
        labels.append(label)
    return sorted(set(labels))


def labels_digest(labels: Iterable[str]) -> str:
    """Returns a stable digest for a canonical label set."""

    canonical = canonicalize_labels(labels)
    contents = "".join(f"{label}\n" for label in canonical).encode()
    return hashlib.sha256(contents).hexdigest()


def shard_for_label(label: str, shard_count: int) -> int:
    """Maps a label to a shard without depending on other labels."""

    if shard_count <= 0:
        raise ValueError("shard count must be positive")
    digest = hashlib.sha256(label.encode()).digest()
    return int.from_bytes(digest, byteorder="big") % shard_count


def partition_labels(
    labels: Iterable[str], shard_index: int, shard_count: int
) -> tuple[list[str], list[str]]:
    """Returns the canonical discovered and selected label sets."""

    if shard_count <= 0:
        raise ValueError("shard count must be positive")
    if shard_index < 0 or shard_index >= shard_count:
        raise ValueError(f"shard index {shard_index} is outside [0, {shard_count})")
    discovered = canonicalize_labels(labels)
    selected = [
        label
        for label in discovered
        if shard_for_label(label, shard_count) == shard_index
    ]
    return discovered, selected


def result_filename(suite: str, shard_index: int, shard_count: int) -> str:
    return f"result-{suite}-{shard_index}-of-{shard_count}.json"


def targets_filename(suite: str, shard_index: int, shard_count: int) -> str:
    return f"targets-{suite}-{shard_index}-of-{shard_count}.txt"


def prepare_partition(
    suite: str,
    shard_index: int,
    shard_count: int,
    labels: Iterable[str],
    output_dir: Path,
) -> tuple[dict, Path, Path]:
    """Writes a shard target manifest and initial result record."""

    if suite not in SUITES:
        raise ValueError(f"unsupported suite: {suite}")
    output_dir.mkdir(parents=True, exist_ok=True)
    errors = []
    try:
        discovered, selected = partition_labels(labels, shard_index, shard_count)
    except ValueError as error:
        discovered = []
        selected = []
        errors.append(str(error))

    if not discovered:
        errors.append("test discovery selected no targets")
    elif not selected:
        errors.append("shard selected no targets")

    target_path = output_dir / targets_filename(suite, shard_index, shard_count)
    target_path.write_text(
        "".join(f"{label}\n" for label in selected), encoding="utf-8"
    )
    record = {
        "schema_version": SCHEMA_VERSION,
        "suite": suite,
        "shard_index": shard_index,
        "shard_count": shard_count,
        "discovered_count": len(discovered),
        "discovered_sha256": labels_digest(discovered),
        "selected_count": len(selected),
        "selected_sha256": labels_digest(selected),
        "passing_tests": 0,
        "exit_code": 4 if errors else None,
        "target_file": target_path.name,
        "errors": errors,
    }
    result_path = output_dir / result_filename(suite, shard_index, shard_count)
    write_json(result_path, record)
    return record, result_path, target_path


def parse_passing_tests(log: str) -> int | None:
    matches = PASSING_TESTS_RE.findall(log)
    return int(matches[-1]) if matches else None


def finalize_result(result_path: Path, log_path: Path, exit_code: int) -> dict:
    """Adds Bazel's outcome to an existing result record."""

    record = read_json(result_path)
    errors = list(record.get("errors", []))
    if record["suite"] in BUILD_SUITES:
        passing_tests = record["selected_count"] if exit_code == 0 else 0
    else:
        passing_tests = parse_passing_tests(
            log_path.read_text(encoding="utf-8", errors="replace")
        )
        if passing_tests is None:
            passing_tests = 0
            if exit_code == 0:
                errors.append("successful Bazel invocation had no test summary")
                exit_code = 4
        if passing_tests > record["selected_count"]:
            errors.append("Bazel passing count exceeds selected target count")
            exit_code = 4
        if exit_code == 0 and passing_tests != record["selected_count"]:
            errors.append(
                "successful Bazel invocation did not pass every selected target"
            )
            exit_code = 4
    record["passing_tests"] = passing_tests
    record["exit_code"] = exit_code
    record["errors"] = errors
    write_json(result_path, record)
    return record


def mark_discovery_failure(result_path: Path, exit_code: int, message: str) -> dict:
    """Records a query or partition failure without running Bazel."""

    record = read_json(result_path)
    record["passing_tests"] = 0
    record["exit_code"] = exit_code if exit_code != 0 else 4
    record["errors"] = list(record.get("errors", [])) + [message]
    write_json(result_path, record)
    return record


def aggregate_results(
    results_dir: Path, expected_shards: dict[str, int]
) -> tuple[dict[str, dict[str, int]], list[str], list[str]]:
    """Validates and aggregates shard records.

    Returns suite outputs, validation errors, and Markdown summary rows.
    """

    records = []
    errors = []
    for result_path in sorted(results_dir.rglob("result-*.json")):
        try:
            record = read_json(result_path)
        except (OSError, json.JSONDecodeError) as error:
            errors.append(f"{result_path.name}: invalid JSON: {error}")
            continue
        record["_result_path"] = result_path
        records.append(record)

    outputs = {}
    summary_rows = []
    for suite, shard_count in expected_shards.items():
        suite_records = [record for record in records if record.get("suite") == suite]
        suite_errors = []
        records_by_index = {}
        for record in suite_records:
            record_error = validate_record_shape(record, suite, shard_count)
            if record_error:
                suite_errors.extend(record_error)
                continue
            shard_index = record["shard_index"]
            if shard_index in records_by_index:
                suite_errors.append(f"duplicate shard index {shard_index}")
            else:
                records_by_index[shard_index] = record

        missing = sorted(set(range(shard_count)) - set(records_by_index))
        if missing:
            suite_errors.append(f"missing shard indexes: {missing}")

        valid_records = [records_by_index[index] for index in sorted(records_by_index)]
        discovered_counts = {record["discovered_count"] for record in valid_records}
        discovered_digests = {record["discovered_sha256"] for record in valid_records}
        if len(discovered_counts) > 1:
            suite_errors.append("shards disagree on discovered target count")
        if len(discovered_digests) > 1:
            suite_errors.append("shards disagree on discovered target digest")

        selected_labels = []
        selected_seen = set()
        passing_tests = 0
        for record in valid_records:
            target_path = record["_result_path"].parent / record["target_file"]
            try:
                labels = canonicalize_labels(
                    target_path.read_text(encoding="utf-8").splitlines()
                )
            except (OSError, ValueError) as error:
                suite_errors.append(
                    f"shard {record['shard_index']} target manifest is invalid: {error}"
                )
                labels = []
            if len(labels) != record["selected_count"]:
                suite_errors.append(
                    f"shard {record['shard_index']} selected count does not match manifest"
                )
            if labels_digest(labels) != record["selected_sha256"]:
                suite_errors.append(
                    f"shard {record['shard_index']} selected digest does not match manifest"
                )
            duplicates = selected_seen.intersection(labels)
            if duplicates:
                suite_errors.append(
                    f"shard {record['shard_index']} overlaps another shard"
                )
            selected_seen.update(labels)
            selected_labels.extend(labels)
            passing_tests += record["passing_tests"]
            if record["exit_code"] != 0:
                suite_errors.append(
                    f"shard {record['shard_index']} exited with {record['exit_code']}"
                )
            suite_errors.extend(
                f"shard {record['shard_index']}: {message}"
                for message in record.get("errors", [])
            )

        # Keep badge outputs deterministic even when inconsistent records make
        # the suite fail validation.
        total_tests = max(discovered_counts, default=0)
        discovered_digest = min(discovered_digests, default=labels_digest([]))
        if len(selected_labels) != total_tests:
            suite_errors.append("selected shard union count does not match discovery")
        if labels_digest(selected_labels) != discovered_digest:
            suite_errors.append("selected shard union digest does not match discovery")
        if passing_tests > total_tests:
            suite_errors.append("aggregate passing count exceeds discovered count")

        exit_code = 1 if suite_errors else 0
        outputs[suite] = {
            "total_tests": total_tests,
            "passing_tests": passing_tests,
            "exit_code": exit_code,
        }
        errors.extend(f"{suite}: {message}" for message in suite_errors)
        status = "PASS" if exit_code == 0 else "FAIL"
        summary_rows.append(
            f"| {suite} | {shard_count} | {passing_tests} / {total_tests} | {status} |"
        )

    unknown_suites = sorted(
        {
            str(record.get("suite"))
            for record in records
            if record.get("suite") not in expected_shards
        }
    )
    if unknown_suites:
        errors.append(f"unexpected suites: {unknown_suites}")
    return outputs, errors, summary_rows


def validate_record_shape(
    record: dict, expected_suite: str, expected_shard_count: int
) -> list[str]:
    errors = []
    required_types = {
        "schema_version": int,
        "suite": str,
        "shard_index": int,
        "shard_count": int,
        "discovered_count": int,
        "discovered_sha256": str,
        "selected_count": int,
        "selected_sha256": str,
        "passing_tests": int,
        "exit_code": int,
        "target_file": str,
        "errors": list,
    }
    for key, expected_type in required_types.items():
        if type(record.get(key)) is not expected_type:
            errors.append(f"record has invalid {key}")
    if errors:
        return errors
    if record["schema_version"] != SCHEMA_VERSION:
        errors.append(f"unsupported schema version {record['schema_version']}")
    if record["suite"] != expected_suite:
        errors.append(f"record has unexpected suite {record['suite']}")
    if record["shard_count"] != expected_shard_count:
        errors.append(
            f"shard count {record['shard_count']} does not match {expected_shard_count}"
        )
    if record["shard_index"] < 0 or record["shard_index"] >= expected_shard_count:
        errors.append(f"shard index {record['shard_index']} is out of range")
    for key in ("discovered_count", "selected_count", "passing_tests", "exit_code"):
        if record[key] < 0:
            errors.append(f"record has negative {key}")
    if record["discovered_count"] == 0:
        errors.append("record discovered no targets")
    if record["selected_count"] == 0:
        errors.append("record selected no targets")
    for key in ("discovered_sha256", "selected_sha256"):
        if re.fullmatch(r"[0-9a-f]{64}", record[key]) is None:
            errors.append(f"record has invalid {key}")
    if Path(record["target_file"]).name != record["target_file"]:
        errors.append("target_file must be a basename")
    if not all(isinstance(message, str) for message in record["errors"]):
        errors.append("record errors must be strings")
    return errors


def read_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, value: dict) -> None:
    with path.open("w", encoding="utf-8") as handle:
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")


def parse_expected_shards(values: list[str]) -> dict[str, int]:
    expected = {}
    for value in values:
        suite, separator, count_text = value.partition("=")
        if not separator or suite not in SUITES:
            raise ValueError(f"invalid expected shard specification: {value}")
        count = int(count_text)
        if count <= 0:
            raise ValueError(f"invalid expected shard count: {value}")
        expected[suite] = count
    if set(expected) != set(SUITES):
        raise ValueError(f"expected shard specifications for {SUITES}")
    return expected


def command_partition(args: argparse.Namespace) -> int:
    labels = args.input.read_text(encoding="utf-8").splitlines()
    record, _, _ = prepare_partition(
        args.suite, args.shard_index, args.shard_count, labels, args.output_dir
    )
    for error in record["errors"]:
        print(f"ERROR: {error}", file=sys.stderr)
    return 0 if not record["errors"] else record["exit_code"]


def command_finalize(args: argparse.Namespace) -> int:
    record = finalize_result(args.result, args.log, args.exit_code)
    for error in record["errors"]:
        print(f"ERROR: {error}", file=sys.stderr)
    return 0 if record["exit_code"] == 0 else record["exit_code"]


def command_discovery_failure(args: argparse.Namespace) -> int:
    record = mark_discovery_failure(args.result, args.exit_code, args.message)
    for error in record["errors"]:
        print(f"ERROR: {error}", file=sys.stderr)
    return record["exit_code"]


def command_aggregate(args: argparse.Namespace) -> int:
    expected = parse_expected_shards(args.expected)
    outputs, errors, rows = aggregate_results(args.results_dir, expected)
    with args.github_output.open("a", encoding="utf-8") as output:
        for suite in SUITES:
            for field in ("total_tests", "passing_tests", "exit_code"):
                output.write(f"{suite}_{field}={outputs[suite][field]}\n")
    with args.step_summary.open("a", encoding="utf-8") as summary:
        summary.write("## Public Bazel test suites\n\n")
        summary.write("| Suite | Shards | Passing | Status |\n")
        summary.write("| --- | ---: | ---: | --- |\n")
        summary.write("\n".join(rows))
        summary.write("\n")
        if errors:
            summary.write("\n### Errors\n\n")
            summary.writelines(f"- {error}\n" for error in errors)
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    return 1 if errors else 0


def command_check(args: argparse.Namespace) -> int:
    expected_suites = set(args.expected_suite)
    records = []
    errors = []
    for result_path in sorted(args.results_dir.glob("result-*.json")):
        try:
            record = read_json(result_path)
        except (OSError, json.JSONDecodeError) as error:
            errors.append(f"{result_path.name}: invalid JSON: {error}")
            continue
        records.append(record)
        if record.get("suite") not in expected_suites:
            errors.append(f"{result_path.name}: unexpected suite {record.get('suite')}")
        if record.get("exit_code") != 0:
            errors.append(
                f"{result_path.name}: exited with {record.get('exit_code', 'missing')}"
            )
        errors.extend(
            f"{result_path.name}: {message}" for message in record.get("errors", [])
        )
    found_suites = {record.get("suite") for record in records}
    missing_suites = sorted(expected_suites - found_suites)
    if missing_suites:
        errors.append(f"missing suite results: {missing_suites}")
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    return 1 if errors else 0


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    partition = subparsers.add_parser("partition")
    partition.add_argument("--suite", choices=SUITES, required=True)
    partition.add_argument("--shard-index", type=int, required=True)
    partition.add_argument("--shard-count", type=int, required=True)
    partition.add_argument("--input", type=Path, required=True)
    partition.add_argument("--output-dir", type=Path, required=True)
    partition.set_defaults(func=command_partition)

    finalize = subparsers.add_parser("finalize")
    finalize.add_argument("--result", type=Path, required=True)
    finalize.add_argument("--log", type=Path, required=True)
    finalize.add_argument("--exit-code", type=int, required=True)
    finalize.set_defaults(func=command_finalize)

    discovery_failure = subparsers.add_parser("discovery-failure")
    discovery_failure.add_argument("--result", type=Path, required=True)
    discovery_failure.add_argument("--exit-code", type=int, required=True)
    discovery_failure.add_argument("--message", required=True)
    discovery_failure.set_defaults(func=command_discovery_failure)

    aggregate = subparsers.add_parser("aggregate")
    aggregate.add_argument("--results-dir", type=Path, required=True)
    aggregate.add_argument("--expected", action="append", required=True)
    aggregate.add_argument("--github-output", type=Path, required=True)
    aggregate.add_argument("--step-summary", type=Path, required=True)
    aggregate.set_defaults(func=command_aggregate)

    check = subparsers.add_parser("check")
    check.add_argument("--results-dir", type=Path, required=True)
    check.add_argument("--expected-suite", action="append", required=True)
    check.set_defaults(func=command_check)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        return args.func(args)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 4


if __name__ == "__main__":
    sys.exit(main())
