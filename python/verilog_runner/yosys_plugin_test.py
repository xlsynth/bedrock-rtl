# SPDX-License-Identifier: Apache-2.0

"""Regression tests for the public Yosys formal plugin."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from cli import Fpv, Synth
from yosys import Yosys, YosysFpv


class YosysPluginTest(unittest.TestCase):
    def make_plugin(self, **kwargs):
        return YosysFpv(
            tclfile_custom_header=None,
            tclfile_custom_body=None,
            env_setup_commands=None,
            **kwargs,
        )

    def test_synthesis_and_fpv_register_separately(self):
        self.assertIs(Yosys.subcommand, Synth)
        self.assertIs(YosysFpv.subcommand, Fpv)
        self.assertEqual(YosysFpv.tool_name, "yosys")

    def test_frontend_preserves_sources_defines_and_parameters(self):
        plugin = self.make_plugin(
            top="arbiter",
            srcs=["rtl/arbiter.sv"],
            hdrs=["include/defs.svh"],
            defines=["BR_ASSERT_ON"],
            params={"Width": "5"},
            analysis_opts=["--single-unit"],
            elab_opts=["--keep-hierarchy"],
            opts=["mode=cover", "depth=12"],
        )
        tcl = plugin.tcl_analysis_elaborate()
        for argument in (
            "rtl/arbiter.sv",
            "-Iinclude",
            "-DBR_ASSERT_ON",
            "-GWidth=5",
            "--no-synthesis-define",
            "-DFORMAL",
            "--keep-hierarchy",
        ):
            self.assertIn(argument, tcl)
        self.assertNotIn("mode=cover", tcl)
        self.assertNotIn("--ignore-assertions", tcl)
        self.assertIn("mode cover", plugin.sby_config())
        self.assertIn("depth 12", plugin.sby_config())
        self.assertIn("smtbmc z3", plugin.sby_config())

    def test_sandbox_script_embeds_configuration_and_backs_up_previous_run(self):
        plugin = self.make_plugin(tclfile="arbiter.tcl", top="arbiter")
        script = plugin.cmd()
        self.assertIn("cat > arbiter.tcl.sby <<'VERILOG_RUNNER_SBY'", script)
        self.assertIn("abc pdr", script)
        self.assertIn("timeout 60", script)
        self.assertIn("model.il arbiter.tcl.il", script)
        self.assertIn("if [ -d arbiter.tcl.sby-work ]; then", script)
        self.assertIn("sby_backup_args=(-b)", script)
        self.assertIn('"${sby_backup_args[@]}" -j 1 -d arbiter.tcl.sby-work', script)
        self.assertIn('"${YOSYS_PATH:-yosys}" -m slang -c arbiter.tcl', script)
        self.assertIn('"${SBY_PATH:-sby}"', script)
        self.assertIn("write_rtlil {arbiter.tcl.il}", plugin.tcl_footer())

    def test_rejects_invalid_configuration(self):
        for option in (
            "mode=invalid",
            "depth=0",
            "timeout=-1",
            "engine=abc pdr\n[script]",
            "unknown=value",
        ):
            with self.subTest(option=option), self.assertRaises(ValueError):
                self.make_plugin(opts=[option])

    def test_elaboration_only_skips_solver(self):
        plugin = self.make_plugin(tclfile="arbiter.tcl", elab_only=True)
        self.assertNotIn("SBY_PATH", plugin.cmd())

    def test_native_success_requires_pass_status_and_zero_return_code(self):
        with tempfile.TemporaryDirectory() as directory:
            plugin = self.make_plugin(
                tclfile=str(Path(directory) / "arbiter.tcl"),
                logfile=str(Path(directory) / "arbiter.log"),
            )
            work_directory = Path(plugin.work_directory)
            work_directory.mkdir()
            status_file = work_directory / "status"
            with patch.object(plugin, "prepare_files"), patch(
                "yosys.run_shell_script"
            ) as run:
                for status, returncode, expected in (
                    ("PASS", 0, True),
                    ("PASS 0 0", 0, True),
                    ("FAIL 2 0", 0, False),
                    ("", 0, False),
                    ("FAIL", 0, False),
                    ("UNKNOWN", 0, False),
                    ("TIMEOUT 0 0", 0, False),
                    ("PASS", 1, False),
                ):
                    with self.subTest(status=status, returncode=returncode):
                        status_file.write_text(status)
                        run.return_value = (returncode, "native console")
                        self.assertEqual(all(plugin.run_cmd().values()), expected)
                status_file.unlink()
                run.return_value = (0, "native console")
                self.assertFalse(all(plugin.run_cmd().values()))


if __name__ == "__main__":
    unittest.main()
