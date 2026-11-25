# SPDX-License-Identifier: Apache-2.0

import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from python.ci.pages_badges import write_badges


class PagesBadgesTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.site = self.root / "site"
        (self.site / "coverage").mkdir(parents=True)
        (self.site / "index.html").write_text("report")
        (self.site / "coverage/index.html").write_text("coverage")
        self.badges = self.site / "badges"
        env = patch.dict(
            os.environ,
            GITHUB_RUN_NUMBER="1",
            GITHUB_SHA="abcdef0" * 5 + "abcde",
            RUNNER_TEMP=temporary.name,
            clear=True,
        )
        env.start()
        self.addCleanup(env.stop)
        git = patch("subprocess.check_output", return_value=b"rtl/top.sv\0")
        git.start()
        self.addCleanup(git.stop)

    def badge(self, name):
        return json.loads((self.badges / f"{name}.json").read_text())

    def test_repeated_restore_replaces_all_counts_but_preserves_report(self):
        os.environ.update(VERILATOR_COUNTS="10/10/0", SLANG_COUNTS="1/1/0")
        write_badges(self.site, restored=False)
        self.assertEqual(self.badge("verilator")["message"], "10 of 10 passing")
        self.assertEqual(self.badge("verilator")["color"], "brightgreen")
        del os.environ["SLANG_COUNTS"]
        os.environ.update(VERILATOR_COUNTS="incomplete", PYTHON_COUNTS="2/3/1")
        for number in ("2", "3"):
            os.environ.update(GITHUB_RUN_NUMBER=number, GITHUB_SHA="1" * 40)
            write_badges(self.site, restored=True)
            self.assertEqual(self.badge("report")["message"], "#1 (abcdef0)")
            self.assertEqual(self.badge("run")["message"], f"#{number} (1111111)")
            self.assertEqual(self.badge("verilator")["message"], "incomplete")
            self.assertEqual(self.badge("slang")["message"], "unavailable")
            self.assertEqual(self.badge("python")["message"], "2 of 3 passing")
            self.assertEqual(self.badge("python")["color"], "red")

    def test_private_counts_only_render_complete_numeric_results(self):
        data = self.root / "badge-counts/proprietary-counts.json"
        data.parent.mkdir()
        data.write_text(
            json.dumps(dict(verific="PRIVATE DETAIL", vcs="3/4/3", ascentlint="2/5/8"))
        )
        os.environ["PRIVATE_COUNTS_READY"] = "true"
        write_badges(self.site, restored=False)
        self.assertEqual(self.badge("verific")["message"], "unavailable")
        self.assertEqual(self.badge("ascentlint")["message"], "incomplete")
        self.assertEqual(self.badge("vcs")["message"], "3 of 4 passing")
        self.assertEqual(self.badge("vcs")["color"], "red")
        self.assertNotIn(
            "PRIVATE DETAIL", "".join(f.read_text() for f in self.badges.iterdir())
        )

    def test_rejects_empty_dashboard(self):
        (self.site / "coverage/index.html").write_text("")
        with self.assertRaisesRegex(ValueError, "coverage/index.html"):
            write_badges(self.site, restored=False)
        self.assertFalse(self.badges.exists())

    def test_rejects_invalid_report_source(self):
        self.badges.mkdir()
        (self.badges / "report.json").write_text('{"message":"unknown"}')
        with self.assertRaisesRegex(ValueError, "Invalid report source"):
            write_badges(self.site, restored=True)
        self.assertFalse((self.badges / "run.json").exists())


if __name__ == "__main__":
    unittest.main()
