# SPDX-License-Identifier: Apache-2.0


"""Unit tests for the cli module."""

import argparse
import unittest
from unittest import mock

from python.verilog_runner.cli import common_args


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
    )
    return args


class TestCliFunctions(unittest.TestCase):

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_sim_includes_split_opts(self):
        common = common_args(_args_for_subcommand("sim"))

        self.assertEqual(common["opts"], ["-foo"])
        self.assertEqual(common["elab_opts"], ["-foo"])
        self.assertEqual(common["sim_opts"], ["+bar=1"])

    @mock.patch.dict("os.environ", {}, clear=True)
    def test_common_args_fpv_omits_sim_only_opts(self):
        common = common_args(_args_for_subcommand("fpv"))

        self.assertEqual(common["opts"], [])
        self.assertNotIn("elab_opts", common)
        self.assertNotIn("sim_opts", common)


if __name__ == "__main__":
    unittest.main()
