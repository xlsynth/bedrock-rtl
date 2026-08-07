# SPDX-License-Identifier: Apache-2.0

"""Unit tests for the public Verilator simulation plugin."""

import unittest

from cli import Sim
from python.verilog_runner.plugins.verilator import Verilator


class VerilatorPluginTest(unittest.TestCase):
    def make_plugin(self, **kwargs):
        defaults = {
            "top": "design",
            "filelist": "design.f",
            "scriptfile": "run.sh",
            "tclfile_custom_header": None,
            "tclfile_custom_body": None,
            "env_setup_commands": None,
        }
        defaults.update(kwargs)
        return Verilator(**defaults)

    def execution_line(self, plugin):
        return next(
            line
            for line in plugin.cmd().splitlines()
            if line.startswith("${VERILATOR_CMD:-verilator}")
        )

    def test_baseline_command_construction(self):
        plugin = self.make_plugin(
            hdrs=["include/defs.svh"],
            defines=["BR_ASSERT_ON"],
            params={"Width": "8"},
            sim_opts=["+seed=1"],
        )

        command = self.execution_line(plugin)

        self.assertIn("--binary --timing --assert -Wno-fatal", command)
        self.assertIn("--top-module design", command)
        self.assertIn("--Mdir obj_dir_design -o simv", command)
        self.assertIn('-LDFLAGS "$libatomic" -f design.f', command)
        self.assertIn("-Iinclude -DBR_VERILATOR -DBR_ASSERT_ON -GWidth=8", command)
        self.assertTrue(command.endswith("&& ./obj_dir_design/simv +seed=1"))
        self.assertIs(Verilator.subcommand, Sim)

    def test_uses_fast_cold_build_flags_by_default(self):
        self.assertIn("-CFLAGS -O0", self.execution_line(self.make_plugin()))

    def test_default_flags_precede_caller_elaboration_options(self):
        command = self.execution_line(
            self.make_plugin(elab_opts=["--output-groups", "2"])
        )

        self.assertLess(
            command.index("-CFLAGS -O0"), command.index("--output-groups 2")
        )

    def test_caller_can_override_default_optimization_level(self):
        command = self.execution_line(self.make_plugin(elab_opts=["-CFLAGS", "-O2"]))

        self.assertLess(command.index("-CFLAGS -O0"), command.rindex("-CFLAGS -O2"))

    def test_coverage_and_waves_flags_are_unchanged(self):
        command = self.execution_line(
            self.make_plugin(waves=True, coverage="coverage.dat")
        )

        build_command, simulation_command = command.split(" && ")
        self.assertIn("--trace", build_command)
        self.assertIn("--coverage", build_command)
        self.assertNotIn("+verilator+coverage", build_command)
        self.assertEqual(
            simulation_command,
            "./obj_dir_design/simv '+verilator+coverage+file+coverage.dat'",
        )

    def test_build_and_simulation_commands_remain_separate(self):
        command = self.execution_line(self.make_plugin())
        build_command, simulation_command = command.split(" && ")

        self.assertTrue(build_command.startswith("${VERILATOR_CMD:-verilator}"))
        self.assertEqual(simulation_command, "./obj_dir_design/simv")
        self.assertNotIn("./obj_dir_design/simv", build_command)

        elaboration_only = self.execution_line(self.make_plugin(elab_only=True))
        self.assertNotIn(" && ", elaboration_only)
        self.assertNotIn("./obj_dir_design/simv", elaboration_only)


if __name__ == "__main__":
    unittest.main()
