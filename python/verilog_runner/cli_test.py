# SPDX-License-Identifier: Apache-2.0


"""Unit tests for the cli module."""

import argparse
import unittest
from unittest import mock

from python.verilog_runner.cli import (
    common_args,
    tcl_file,
    tcl_fragment_file,
    validate_top,
)


def _args_for_subcommand(subcommand: str) -> argparse.Namespace:
    args = argparse.Namespace(
        hdr=[],
        data=["image.mem"],
        define=[],
        params={},
        opt=[],
        analysis_opt=["--ignore-initial"],
        elab_opt=["-foo"],
        sim_opt=["+bar=1"],
        srcs=["tb.sv"],
        top="tb",
        tcl="run.tcl",
        script="run.sh",
        log="run.log",
        filelist="sources.f",
        custom_control_header=None,
        custom_control_body=None,
        custom_tcl_header=None,
        custom_tcl_body=None,
        subcommand=subcommand,
        tool="verilator",
    )
    return args


class TestCliFunctions(unittest.TestCase):

    def test_control_file_accepts_sby_extension(self):
        self.assertEqual(tcl_file("job.sby"), "job.sby")

    def test_tcl_alias_rejects_sby_extension(self):
        with self.assertRaises(argparse.ArgumentTypeError):
            tcl_fragment_file("job.sby")

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
    def test_common_args_fpv_leaves_plugin_specific_opts_to_plugin(self):
        common = common_args(_args_for_subcommand("fpv"))

        self.assertEqual(common["data"], ["image.mem"])
        self.assertEqual(common["opts"], [])
        self.assertNotIn("analysis_opts", common)
        self.assertNotIn("elab_opts", common)
        self.assertNotIn("sim_opts", common)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_synth_includes_mapping_options(self):
        args = _args_for_subcommand("synth")
        args.liberty = "cells.lib"
        args.clock_period_ps = 1000

        common = common_args(args)

        self.assertEqual(common["liberty"], "cells.lib")
        self.assertEqual(common["clock_period_ps"], 1000)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_preserves_tool_opts(self):
        args = _args_for_subcommand("fpv")
        args.opt = ["-legacy"]

        common = common_args(args)

        self.assertEqual(common["opts"], ["-legacy"])

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_accepts_generic_control_fragments(self):
        args = _args_for_subcommand("fpv")
        args.tool = "sby"
        args.custom_control_header = "header.sby"
        args.custom_control_body = "body.sby"

        common = common_args(args)

        self.assertEqual(common["tclfile_custom_header"], "header.sby")
        self.assertEqual(common["tclfile_custom_body"], "body.sby")

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_accepts_tcl_specific_aliases(self):
        args = _args_for_subcommand("fpv")
        args.tool = "jg"
        args.custom_tcl_header = "header.tcl"
        args.custom_tcl_body = "body.tcl"

        common = common_args(args)

        self.assertEqual(common["tclfile_custom_header"], "header.tcl")
        self.assertEqual(common["tclfile_custom_body"], "body.tcl")

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_rejects_duplicate_control_aliases(self):
        args = _args_for_subcommand("fpv")
        args.custom_control_header = "header.sby"
        args.custom_tcl_header = "header.tcl"

        with self.assertRaisesRegex(ValueError, "aliases; specify only one"):
            common_args(args)

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_rejects_tcl_alias_for_sby(self):
        args = _args_for_subcommand("fpv")
        args.tool = "sby"
        args.custom_tcl_body = "body.tcl"

        with self.assertRaisesRegex(ValueError, "SBY control fragments"):
            common_args(args)

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
