# SPDX-License-Identifier: Apache-2.0

"""Pinned ASAP7 synthesis profile used by Bedrock PPA sweeps."""

load("//bazel:verilog.bzl", "verilog_yosys_synth_suite")

# These inputs match the OpenROAD-flow-scripts ASAP7 platform at commit
# ae9a8ed9d67b087abffd4645208672a33da2d3bf. ASAP7 splits the RVT/TT NLDM
# standard cells across five files; all five are needed for mapping and area.
# Source: flow/platforms/asap7/config.mk in that pinned revision.
_LIBERTIES = [
    "lib/NLDM/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib.gz",
    "lib/NLDM/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib.gz",
    "lib/NLDM/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib.gz",
    "lib/NLDM/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib",
    "lib/NLDM/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib.gz",
]

# Sequential cells are distributed in the SEQ file, so identify it separately
# for the synthesis plugin's sequential-cell mapping phase.
_SEQUENTIAL_LIBERTY = "lib/NLDM/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib"

# Match the representative input driver and output load used by the pinned
# OpenROAD ASAP7 platform: ABC_DRIVER_CELL and ABC_LOAD_IN_FF in the same
# config.mk. These are profile assumptions, not properties of the Bazel rule.
_INPUT_DRIVER_CELL = "BUFx2_ASAP7_75t_R"
_OUTPUT_LOAD_FF = "3.898"

_SHA256 = {
    "lib/NLDM/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib.gz": "fe9f1c18e88ab129d63ad82adc256f3a85c7e38e47dabbe0a96749b41087dea1",
    "lib/NLDM/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib.gz": "8d6db2c2f83c3c162be54a5e102b2d379fcaaaef2db5f0b1d4152c395d01fea1",
    "lib/NLDM/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib.gz": "bbe6d904d58c7367de1ed7639e4eae386c65fa0a5af26ae62dc5e4e2ec52b08b",
    "lib/NLDM/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib": "57a0b403485b99ebd676942af4673ac086b86c7c75fbdc3e5c0038501dd22ba3",
    "lib/NLDM/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib.gz": "073ac4b6b08f272b6953b0ad54d1d9743767a7d15a0e2964ed86cf44c3dbe00e",
}

def asap7_rvt_tt_yosys_synth_suite(name, defines, deps, tags, top, **kwargs):
    """Creates the Yosys ASAP7 RVT/TT synthesis targets for one sweep."""
    verilog_yosys_synth_suite(
        name = name,
        defines = defines,
        deps = deps,
        input_driver_cell = _INPUT_DRIVER_CELL,
        liberties = _LIBERTIES,
        library_name = "asap7_rvt_tt",
        liberty_root = "${ASAP7_ROOT}",
        liberty_sha256 = _SHA256,
        output_load_ff = _OUTPUT_LOAD_FF,
        sandbox_tags = tags + ["ppa-synth-asap7-rvt-tt", "ppa-synth-sandbox"],
        sequential_liberty = _SEQUENTIAL_LIBERTY,
        synth_profile = "asap7-rvt-tt",
        tags = tags + ["ppa-synth", "ppa-synth-asap7-rvt-tt"],
        top = top,
        **kwargs
    )
