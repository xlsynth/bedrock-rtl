# SPDX-License-Identifier: Apache-2.0

import json
from pathlib import Path
import tempfile
import unittest

from python.ppa.generate_ppa import (
    parse_log,
    render_markdown,
    validate_catalog_coverage,
)


class GeneratePpaTest(unittest.TestCase):
    def test_parse_and_render_generic_yosys_report(self):
        metadata = {"top": "dut", "params": {"Width": "32"}}
        stats = {
            "modules": {
                "\\dut": {
                    "num_cells": 12,
                    "num_cells_by_type": {"$_DFF_P_": 4, "$_AND_": 8},
                    "num_memory_bits": 0,
                    "num_wire_bits": 37,
                }
            }
        }
        log = "\n".join(
            [
                "Yosys 0.65 (git sha1 test)",
                "Longest topological path in dut (length=7):",
                "PPA_METADATA_JSON_BEGIN",
                json.dumps(metadata),
                "PPA_METADATA_JSON_END",
                "PPA_STAT_JSON_BEGIN",
                json.dumps(stats),
                "PPA_STAT_JSON_END",
            ]
        )

        metric = parse_log("//foo:dut_synth", log)

        self.assertEqual(metric.cells, 12)
        self.assertEqual(metric.flops, 4)
        self.assertEqual(metric.logic_depth, 7)
        self.assertEqual(metric.tool_version, "Yosys 0.65 (git sha1 test)")
        rendered = render_markdown([metric])
        self.assertIn("`dut`", rendered)
        self.assertIn("`Width=32`", rendered)
        self.assertIn("| 12 | 4 | 37 |", rendered)
        self.assertIn("Tool versions: `Yosys 0.65 (git sha1 test)`", rendered)
        self.assertIn("The design hierarchy is flattened before measurement", rendered)
        self.assertIn("**Cells:**", rendered)
        self.assertIn("**Flops:**", rendered)
        self.assertIn("**Wire bits:**", rendered)
        self.assertIn("**Logic depth:**", rendered)
        self.assertNotIn("Memory bits", rendered)
        self.assertIn("N/A", rendered)

    def test_rejects_missing_markers(self):
        with self.assertRaisesRegex(ValueError, "missing PPA_METADATA_JSON_BEGIN"):
            parse_log("//foo:bad", "Yosys 0.65")

    def test_parse_and_render_asap7_report(self):
        metadata = {
            "top": "dut",
            "params": {"Width": "32"},
            "synth_profile": "asap7-rvt-tt",
            "liberties": ["lib/NLDM/asap7.lib.gz"],
        }
        stats = {
            "modules": {
                "\\dut": {
                    "num_cells": 9,
                    "num_cells_by_type": {
                        "DFFHQNx1_ASAP7_75t_R": 4,
                        "NAND2xp5_ASAP7_75t_R": 5,
                    },
                    "num_wire_bits": 42,
                }
            }
        }
        log = "\n".join(
            [
                "Yosys 0.65 (git sha1 test)",
                "Longest topological path in dut (length=6):",
                "ABC: WireLoad = none Area = 1.25 Delay = 23.5 ps",
                "Chip area for module '\\dut': 1.25",
                "PPA_METADATA_JSON_BEGIN",
                json.dumps(metadata),
                "PPA_METADATA_JSON_END",
                "PPA_STAT_JSON_BEGIN",
                json.dumps(stats),
                "PPA_STAT_JSON_END",
            ]
        )

        metric = parse_log("//foo:dut_synth_yosys_asap7_rvt_tt", log)

        self.assertEqual(metric.synth_profile, "asap7-rvt-tt")
        self.assertEqual(metric.cells, 9)
        self.assertEqual(metric.flops, 4)
        self.assertEqual(metric.logic_depth, 6)
        self.assertEqual(metric.mapped_area, 1.25)
        self.assertEqual(metric.mapped_delay, 23.5)
        rendered = render_markdown([metric])
        self.assertIn("ASAP7 RVT/TT", rendered)
        self.assertIn("Mapped cells", rendered)
        self.assertIn("ABC delay (ps)", rendered)
        self.assertIn("`asap7.lib.gz`", rendered)

    def test_catalog_coverage_rejects_missing_module(self):
        with tempfile.TemporaryDirectory() as temporary:
            libraries = Path(temporary) / "LIBRARIES.md"
            libraries.write_text(
                "| Module | Description | Verification artifacts |\n"
                "| --- | --- | --- |\n"
                "| `br_present` | Present module. | Elab/lint. |\n"
                "| `br_missing` | Missing module. | Elab/lint. |\n",
                encoding="utf-8",
            )
            metric = self._metric("br_present")
            with self.assertRaisesRegex(ValueError, "br_missing"):
                validate_catalog_coverage([metric], libraries)

    @staticmethod
    def _metric(top):
        from python.ppa.generate_ppa import PpaMetrics

        return PpaMetrics(
            target="//foo:synth",
            top=top,
            params={},
            synth_profile="generic",
            tool_version="Yosys 0.65",
            liberties=(),
            cells=1,
            flops=0,
            wire_bits=1,
            logic_depth=1,
            mapped_area=None,
            mapped_delay=None,
        )


if __name__ == "__main__":
    unittest.main()
