# SPDX-License-Identifier: Apache-2.0

import argparse
import unittest

from yosys import (
    Yosys,
    _liberty_file,
    _unconstrained_abc_script,
)


class YosysTest(unittest.TestCase):
    def test_unconstrained_abc_script_is_readable_and_stable(self):
        self.assertEqual(
            _unconstrained_abc_script(None),
            "+strash;&get,-n;&fraig,-x;&put;scorr;dc2;dretime;strash;"
            "&get,-n;&dch,-f;&nf;&put;stime,-p",
        )
        self.assertIn("&nf,-D,1000", _unconstrained_abc_script(1000))

    def test_liberty_file_must_be_relative_to_root(self):
        self.assertEqual(_liberty_file("lib/cells.lib.gz"), "lib/cells.lib.gz")
        with self.assertRaises(argparse.ArgumentTypeError):
            _liberty_file("/opt/pdk/cells.lib")

    def test_liberty_root_is_materialized_in_generated_scripts(self):
        yosys = Yosys(
            top="dut",
            logfile="dut.log",
            tclfile_custom_header=None,
            tclfile_custom_body=None,
            env_setup_commands=None,
            liberties=["lib/cells.lib", "lib/cells_seq.lib"],
            sequential_liberty="lib/cells_seq.lib",
            liberty_root="/opt/example-pdk",
            liberty_sha256={
                "lib/cells.lib": "a" * 64,
                "lib/cells_seq.lib": "b" * 64,
            },
        )

        tcl = yosys.default_tcl_body()
        shell = yosys.cmd()

        self.assertIn("{/opt/example-pdk/lib/cells.lib}", tcl)
        self.assertIn("{/opt/example-pdk/lib/cells_seq.lib}", tcl)
        self.assertNotIn("$::env", tcl)
        self.assertIn("/opt/example-pdk/lib/cells.lib", shell)


if __name__ == "__main__":
    unittest.main()
