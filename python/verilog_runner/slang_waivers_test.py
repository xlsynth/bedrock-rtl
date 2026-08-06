# SPDX-License-Identifier: Apache-2.0

"""Tests source-local Slang waiver scope validation."""

from pathlib import Path
import tempfile
import unittest

from python.verilog_runner.slang_waivers import check_file


class SlangWaiversTest(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "design.sv"
            path.write_text(source, encoding="utf-8")
            return check_file(str(path))

    def test_accepts_scoped_waiver(self):
        errors = self.check(
            "// slang lint_save\n"
            "// slang lint_off unused-port\n"
            "input logic unused;\n"
            "// slang lint_restore\n"
        )
        self.assertEqual(errors, [])

    def test_rejects_waiver_without_saved_scope(self):
        self.assertIn(
            "lint_off requires lint_save",
            self.check("// slang lint_off unused-port\n")[0],
        )

    def test_rejects_unclosed_scope(self):
        errors = self.check("// slang lint_save\n// slang lint_off unused-port\n")
        self.assertIn("lint_save has no lint_restore", errors[0])

    def test_rejects_restore_without_saved_scope(self):
        self.assertIn(
            "lint_restore has no lint_save", self.check("// slang lint_restore\n")[0]
        )

    def test_rejects_lint_on(self):
        self.assertIn(
            "use lint_restore", self.check("// slang lint_on unused-port\n")[0]
        )

    def test_rejects_saved_scope_without_waiver(self):
        errors = self.check("// slang lint_save\n// slang lint_restore\n")
        self.assertIn("lint_save has no lint_off", errors[0])


if __name__ == "__main__":
    unittest.main()
