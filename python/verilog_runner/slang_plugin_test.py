# SPDX-License-Identifier: Apache-2.0

"""Unit tests for the public slang elaboration and lint plugins."""

import argparse
import unittest

from cli import Elab, Lint
from python.verilog_runner.plugins.slang import Slang, SlangLint


class SlangPluginTest(unittest.TestCase):
    def make_plugin(self, plugin_type, **kwargs):
        return plugin_type(
            tclfile_custom_header=None,
            tclfile_custom_body=None,
            env_setup_commands=None,
            **kwargs,
        )

    def test_plugins_register_for_separate_subcommands(self):
        self.assertIs(Slang.subcommand, Elab)
        self.assertIs(SlangLint.subcommand, Lint)
        self.assertEqual(Slang.tool_name, "slang")
        self.assertEqual(SlangLint.tool_name, "slang")

    def test_elaboration_preserves_top_and_common_arguments(self):
        plugin = self.make_plugin(
            Slang,
            top="design",
            filelist="design.f",
            hdrs=["include/defs.svh"],
            defines=["BR_ASSERT_ON"],
            params={"Width": "8"},
            opts=["--compat=all"],
            scriptfile="run.sh",
        )

        command = plugin.cmd()

        self.assertIn("-f design.f", command)
        self.assertIn("--top design", command)
        self.assertIn("-Iinclude", command)
        self.assertIn("-DBR_ASSERT_ON", command)
        self.assertIn("-GWidth=8", command)
        self.assertIn("--compat=all", command)
        self.assertNotIn("--lint-only", command)
        self.assertNotIn("-F ", command)

    def test_compile_only_elaboration_preserves_lint_only_flag(self):
        plugin = self.make_plugin(
            Slang, filelist="design.f", compile_only=True, scriptfile="run.sh"
        )

        command = plugin.cmd()

        self.assertIn("--lint-only", command)
        self.assertNotIn("--top", command)

    def test_lint_fully_elaborates_and_uses_policy(self):
        plugin = self.make_plugin(
            SlangLint,
            top="design",
            filelist="design.f",
            policy="bazel/slang_lint_policy.f",
            scriptfile="run.sh",
        )

        command = plugin.cmd()

        self.assertIn("--top design", command)
        self.assertIn("-F bazel/slang_lint_policy.f", command)
        self.assertNotIn("--lint-only", command)
        self.assertNotIn("--disable-analysis", command)

    def test_lint_quotes_policy_paths(self):
        plugin = self.make_plugin(
            SlangLint,
            top="design",
            filelist="design.f",
            policy="lint policies/strict.f",
            scriptfile="run.sh",
        )

        self.assertIn("-F 'lint policies/strict.f'", plugin.cmd())

    def test_lint_accepts_existing_runner_policy_argument(self):
        args = argparse.Namespace(
            hdr=[],
            define=[],
            params={},
            opt=[],
            srcs=["design.sv"],
            top="design",
            tcl="run.tcl",
            script="run.sh",
            log="run.log",
            filelist="design.f",
            custom_tcl_header=None,
            custom_tcl_body=None,
            subcommand="lint",
            tool="slang",
            policy="strict.f",
        )

        self.assertEqual(SlangLint.from_args(args).policy, "strict.f")


if __name__ == "__main__":
    unittest.main()
