# SPDX-License-Identifier: Apache-2.0


"""Unit tests for the cli module."""

import argparse
import unittest
from unittest import mock

from python.verilog_runner.cli import common_args, validate_top


def _args_for_subcommand(subcommand: str) -> argparse.Namespace:
    args = argparse.Namespace(
        hdr=[],
        define=[],
        params={},
        opt=[],
        elab_opt=["-foo"],
        sim_opt=["+bar=1"],
        srcs=["tb.sv"],
        top="tb",
        tcl="run.tcl",
        script="run.sh",
        log="run.log",
        filelist="sources.f",
        custom_tcl_header=None,
        custom_tcl_body=None,
        subcommand=subcommand,
        tool="verilator",
    )
    return args


class TestCliFunctions(unittest.TestCase):

    def test_validate_top_allows_compile_only_elab_without_top(self):
        args = _args_for_subcommand("elab")
        args.top = None
        args.compile_only = True

        validate_top(argparse.ArgumentParser(), args)

    def test_validate_top_rejects_non_compile_only_elab_without_top(self):
        args = _args_for_subcommand("elab")
        args.top = None
        args.compile_only = False

        with self.assertRaises(SystemExit):
            validate_top(argparse.ArgumentParser(), args)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_sim_includes_split_opts(self):
        common = common_args(_args_for_subcommand("sim"))

        self.assertEqual(common["opts"], [])
        self.assertEqual(common["elab_opts"], ["-foo"])
        self.assertEqual(common["sim_opts"], ["+bar=1"])

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_fpv_omits_sim_only_opts(self):
        common = common_args(_args_for_subcommand("fpv"))

        self.assertEqual(common["opts"], [])
        self.assertNotIn("elab_opts", common)
        self.assertNotIn("sim_opts", common)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_synth_includes_mapping_options(self):
        args = _args_for_subcommand("synth")
        args.liberty = ["lib/a.lib", "lib/b.lib.gz"]
        args.dff_liberty = "lib/a.lib"
        args.liberty_root_env = "PDK_ROOT"
        args.liberty_sha256 = [("lib/a.lib", "a" * 64)]
        args.synth_profile = "example-tt"
        args.clock_period_ps = 1000
        args.abc_driver_cell = "BUFx2_EXAMPLE"
        args.abc_load_ff = 3.898

        common = common_args(args)

        self.assertEqual(common["liberties"], ["lib/a.lib", "lib/b.lib.gz"])
        self.assertEqual(common["dff_liberty"], "lib/a.lib")
        self.assertEqual(common["liberty_root_env"], "PDK_ROOT")
        self.assertEqual(common["liberty_sha256"], {"lib/a.lib": "a" * 64})
        self.assertEqual(common["synth_profile"], "example-tt")
        self.assertEqual(common["clock_period_ps"], 1000)
        self.assertEqual(common["abc_driver_cell"], "BUFx2_EXAMPLE")
        self.assertEqual(common["abc_load_ff"], 3.898)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_preserves_tool_opts(self):
        args = _args_for_subcommand("fpv")
        args.opt = ["-legacy"]

        common = common_args(args)

        self.assertEqual(common["opts"], ["-legacy"])

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_sim_rejects_tool_opts_for_non_vcs(self):
        args = _args_for_subcommand("sim")
        args.opt = ["-legacy"]

        with self.assertRaisesRegex(ValueError, "legacy VCS-only"):
            common_args(args)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_sim_preserves_tool_opts_for_vcs(self):
        args = _args_for_subcommand("sim")
        args.tool = "vcs"
        args.opt = ["-legacy"]

        common = common_args(args)

        self.assertEqual(common["opts"], ["-legacy"])
        self.assertEqual(common["elab_opts"], ["-foo"])
        self.assertEqual(common["sim_opts"], ["+bar=1"])


if __name__ == "__main__":
    unittest.main()
