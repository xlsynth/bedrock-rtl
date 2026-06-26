# SPDX-License-Identifier: Apache-2.0

import argparse
from contextlib import redirect_stderr
import io
import json
from pathlib import Path
import tempfile
import unittest

from python.ci.bazel_oss_sharding import (
    aggregate_results,
    canonicalize_labels,
    command_check,
    finalize_result,
    labels_digest,
    partition_labels,
    prepare_partition,
    shard_for_label,
)


class BazelOssShardingTest(unittest.TestCase):
    def test_canonicalizes_labels(self):
        self.assertEqual(
            canonicalize_labels(["//z:test\n", "", "//a:test", "//z:test"]),
            ["//a:test", "//z:test"],
        )
        with self.assertRaisesRegex(ValueError, "invalid Bazel label"):
            canonicalize_labels(["not-a-label"])

    def test_partitions_are_disjoint_and_complete(self):
        labels = [f"//pkg:test_{index}" for index in range(100)]
        shards = [partition_labels(labels, index, 7)[1] for index in range(7)]
        flattened = [label for shard in shards for label in shard]
        self.assertEqual(sorted(flattened), sorted(labels))
        self.assertEqual(len(flattened), len(set(flattened)))

    def test_adding_label_does_not_move_existing_labels(self):
        labels = [f"//pkg:test_{index}" for index in range(30)]
        assignments = {label: shard_for_label(label, 4) for label in labels}
        labels.append("//pkg:new_test")
        updated = {label: shard_for_label(label, 4) for label in labels}
        for label, shard in assignments.items():
            self.assertEqual(updated[label], shard)

    def test_rejects_invalid_shard_coordinates(self):
        with self.assertRaisesRegex(ValueError, "positive"):
            partition_labels(["//pkg:test"], 0, 0)
        with self.assertRaisesRegex(ValueError, "outside"):
            partition_labels(["//pkg:test"], 2, 2)

    def test_prepare_rejects_empty_discovery_and_empty_shard(self):
        with tempfile.TemporaryDirectory() as temporary:
            output_dir = Path(temporary)
            empty, _, _ = prepare_partition("slang", 0, 1, [], output_dir)
            self.assertNotEqual(empty["exit_code"], 0)
            self.assertIn("test discovery selected no targets", empty["errors"])

            label = "//pkg:single_test"
            selected_index = shard_for_label(label, 2)
            empty_index = 1 - selected_index
            record, _, _ = prepare_partition(
                "slang", empty_index, 2, [label], output_dir
            )
            self.assertIn("shard selected no targets", record["errors"])

    def test_finalize_parses_success_and_rejects_missing_summary(self):
        with tempfile.TemporaryDirectory() as temporary:
            output_dir = Path(temporary)
            _, result_path, _ = prepare_partition(
                "python", 0, 1, ["//python:test"], output_dir
            )
            log_path = output_dir / "bazel.log"
            log_path.write_text("Executed 1 out of 1 test: 1 test passes.\n")
            record = finalize_result(result_path, log_path, 0)
            self.assertEqual(record["passing_tests"], 1)
            self.assertEqual(record["exit_code"], 0)

            log_path.write_text("no summary\n")
            record = finalize_result(result_path, log_path, 0)
            self.assertNotEqual(record["exit_code"], 0)

    def test_aggregate_accepts_complete_partition(self):
        with tempfile.TemporaryDirectory() as temporary:
            results_dir = Path(temporary)
            self._write_suite(results_dir, "python", 1, ["//python:test"])
            self._write_suite(results_dir, "stardoc", 1, ["//bazel:test"])
            self._write_suite(
                results_dir,
                "slang",
                2,
                [f"//rtl:slang_{index}" for index in range(20)],
            )
            self._write_suite(
                results_dir,
                "verilator",
                3,
                [f"//sim:verilator_{index}" for index in range(30)],
            )

            outputs, errors, _ = aggregate_results(
                results_dir,
                {"python": 1, "stardoc": 1, "slang": 2, "verilator": 3},
            )

            self.assertEqual(errors, [])
            self.assertEqual(outputs["slang"]["total_tests"], 20)
            self.assertEqual(outputs["verilator"]["passing_tests"], 30)

    def test_aggregate_rejects_missing_duplicate_and_inconsistent_shards(self):
        with tempfile.TemporaryDirectory() as temporary:
            results_dir = Path(temporary)
            paths = self._write_suite(
                results_dir,
                "slang",
                2,
                [f"//rtl:test_{index}" for index in range(20)],
            )
            paths[1].unlink()
            self._write_suite(results_dir, "python", 1, ["//python:test"])
            self._write_suite(results_dir, "stardoc", 1, ["//bazel:test"])
            self._write_suite(results_dir, "verilator", 1, ["//sim:test"])

            _, errors, _ = aggregate_results(
                results_dir,
                {"python": 1, "stardoc": 1, "slang": 2, "verilator": 1},
            )
            self.assertTrue(any("missing shard indexes" in error for error in errors))

            duplicate = results_dir / "duplicate"
            duplicate.mkdir()
            duplicate_result = duplicate / paths[0].name
            duplicate_result.write_text(paths[0].read_text(encoding="utf-8"))
            target_name = json.loads(paths[0].read_text())["target_file"]
            (duplicate / target_name).write_text(
                (results_dir / target_name).read_text(encoding="utf-8")
            )
            _, errors, _ = aggregate_results(
                results_dir,
                {"python": 1, "stardoc": 1, "slang": 2, "verilator": 1},
            )
            self.assertTrue(any("duplicate shard index" in error for error in errors))

    def test_aggregate_rejects_manifest_tampering(self):
        with tempfile.TemporaryDirectory() as temporary:
            results_dir = Path(temporary)
            self._write_suite(results_dir, "python", 1, ["//python:test"])
            self._write_suite(results_dir, "stardoc", 1, ["//bazel:test"])
            paths = self._write_suite(results_dir, "slang", 1, ["//rtl:a", "//rtl:b"])
            self._write_suite(results_dir, "verilator", 1, ["//sim:test"])
            record = json.loads(paths[0].read_text(encoding="utf-8"))
            (results_dir / record["target_file"]).write_text("//rtl:a\n")

            _, errors, _ = aggregate_results(
                results_dir,
                {"python": 1, "stardoc": 1, "slang": 1, "verilator": 1},
            )
            self.assertTrue(any("does not match manifest" in error for error in errors))
            self.assertTrue(any("union digest" in error for error in errors))

    def test_aggregate_rejects_inconsistent_discovery(self):
        with tempfile.TemporaryDirectory() as temporary:
            results_dir = Path(temporary)
            self._write_suite(results_dir, "python", 1, ["//python:test"])
            self._write_suite(results_dir, "stardoc", 1, ["//bazel:test"])
            paths = self._write_suite(
                results_dir,
                "slang",
                2,
                [f"//rtl:test_{index}" for index in range(20)],
            )
            self._write_suite(results_dir, "verilator", 1, ["//sim:test"])
            record = json.loads(paths[1].read_text(encoding="utf-8"))
            record["discovered_sha256"] = "0" * 64
            paths[1].write_text(json.dumps(record), encoding="utf-8")

            _, errors, _ = aggregate_results(
                results_dir,
                {"python": 1, "stardoc": 1, "slang": 2, "verilator": 1},
            )
            self.assertTrue(
                any("discovered target digest" in error for error in errors)
            )

    def test_check_requires_successful_expected_suites(self):
        with tempfile.TemporaryDirectory() as temporary:
            results_dir = Path(temporary)
            paths = self._write_suite(results_dir, "python", 1, ["//python:test"])
            args = argparse.Namespace(
                results_dir=results_dir, expected_suite=["python", "stardoc"]
            )
            with redirect_stderr(io.StringIO()):
                self.assertEqual(command_check(args), 1)

            record = json.loads(paths[0].read_text(encoding="utf-8"))
            record["exit_code"] = 7
            paths[0].write_text(json.dumps(record), encoding="utf-8")
            args.expected_suite = ["python"]
            with redirect_stderr(io.StringIO()):
                self.assertEqual(command_check(args), 1)

    @staticmethod
    def _write_suite(
        output_dir: Path, suite: str, shard_count: int, labels: list[str]
    ) -> list[Path]:
        result_paths = []
        for shard_index in range(shard_count):
            record, result_path, _ = prepare_partition(
                suite, shard_index, shard_count, labels, output_dir
            )
            if record["errors"]:
                raise AssertionError(record["errors"])
            record["passing_tests"] = record["selected_count"]
            record["exit_code"] = 0
            result_path.write_text(
                json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            result_paths.append(result_path)
        return result_paths


if __name__ == "__main__":
    unittest.main()
