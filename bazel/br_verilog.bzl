# SPDX-License-Identifier: Apache-2.0

"""Bedrock-internal Verilog rules for Bazel."""

load("//bazel:asap7.bzl", "asap7_rvt_tt_yosys_synth_suite")
load("//bazel:verilog.bzl", "verilog_elab_and_lint_test_suite", "verilog_fpv_test_suite", "verilog_sim_test_suite", "verilog_yosys_synth_suite")

def br_verilog_elab_and_lint_test_suite(name, **kwargs):
    """Wraps three instances of verilog_elab_and_lint_test_suite.

    Not intended to be called by Bedrock users.

    (1) The first instance defines "BR_ASSERT_ON" and uses the provided name.
        This is to test the design is elab/lint clean when it will be integrated into a user's design.
    (2) The second instance defines "BR_ASSERT_ON" and "BR_ENABLE_IMPL_CHECKS".
        This is to test the design is elab/lint clean with all Bedrock-internal assertions enabled.
    (3) The third instance has no defines.
        This is to test the design is elab/lint clean without any assertions.

    Args:
        name (str): The base name of the test suite.
        **kwargs: Additional keyword arguments passed to verilog_elab_and_lint_test_suite. Do not pass defines.
    """

    if "defines" in kwargs:
        fail("Do not pass defines to br_verilog_elab_and_lint_test_suite. They are hard-coded in the macro.")

    verilog_elab_and_lint_test_suite(
        name = name,
        defines = ["BR_ASSERT_ON"],
        tags = ["assert"],
        **kwargs
    )

    verilog_elab_and_lint_test_suite(
        name = name + "_allassert",
        defines = ["BR_ASSERT_ON", "BR_ENABLE_IMPL_CHECKS"],
        tags = ["allassert"],
        **kwargs
    )

    verilog_elab_and_lint_test_suite(
        name = name + "_noassert",
        defines = [],
        tags = ["noassert"],
        **kwargs
    )

def br_verilog_sim_test_suite(name, tool, defines = None, elab_opts = [], sim_opts = [], **kwargs):
    """Wraps verilog_sim_test_suite with Bedrock-internal settings. Not intended to be called by Bedrock users.

    * Defines `BR_ASSERT_ON`, `BR_ENABLE_IMPL_CHECKS`, and `SIMULATION` by default.
    * Sets tool to exit on first assertion failure.

    Args:
        name (str): The base name of the test suite.
        tool (str): The simulator tool to use.
        defines (List[str] or None): Defines to pass to the simulator. If omitted, Bedrock's simulation defaults
            are used. Pass an empty list to compile without any defines.
        elab_opts (List[str]): Compile/elaboration options to pass to the simulator.
        sim_opts (List[str]): Simulation runtime options to pass to the simulator.
        **kwargs: Additional keyword arguments passed to verilog_sim_test_suite.
    """

    if tool == "vcs":
        elab_opts = elab_opts + ["-assert global_finish_maxfail=1+offending_values"]

    if defines == None:
        defines = ["BR_ASSERT_ON", "BR_ENABLE_IMPL_CHECKS", "SIMULATION"]

    verilog_sim_test_suite(
        name = name,
        tool = tool,
        elab_opts = elab_opts,
        sim_opts = sim_opts,
        defines = defines,
        **kwargs
    )

def br_verilog_sim_test_tools_suite(name, tools = [], coverage = None, **kwargs):
    """Wraps br_verilog_sim_test_suite with multiple simulation tools.

    Args:
        name (str): The base name of the test suite.
        tools (list of strings): simulator tools to use.
        coverage (bool or None): If true, gathers coverage data from all tests in the test suite.
            If None, the coverage will be enabled if Verilator is used.
        **kwargs: Additional keyword arguments passed to br_verilog_sim_test_suite.
    """
    if coverage and "verilator" not in tools:
        fail("coverage = True is currently supported only by Verilator.")

    if coverage == None and "verilator" in tools and not kwargs.get("elab_only", False):
        coverage = True

    for tool in tools:
        tool_kwargs = {}
        tool_kwargs.update(kwargs)
        tool_kwargs["coverage"] = coverage and tool == "verilator"

        br_verilog_sim_test_suite(
            name = name + "_" + tool,
            tool = tool,
            **tool_kwargs
        )

def br_verilog_yosys_synth_suite(
        name,
        defines = ["SYNTHESIS"],
        deps = [],
        gate_library = "//gate/rtl:br_gate_mock",
        structured_gate_library = "//mux/rtl:br_mux_bin_structured_gates",
        tags = [],
        top = None,
        **kwargs):
    """Creates generic and ASAP7 Yosys sweeps for representative parameters.

    Args:
        name (str): Base name of the generated synthesis targets.
        defines (list[str]): Synthesis preprocessor defines.
        deps (list[label]): Verilog library dependencies.
        gate_library (label): Generic gate model used for no-PDK Yosys PPA runs.
        structured_gate_library (label): Generic structured-gate mux implementation used by the no-PDK Yosys flow.
        tags (list[str]): Additional Bazel tags.
        top (str): Top module. Defaults to the target name of the sole explicit dependency.
        **kwargs: Additional arguments passed to verilog_synth_suite.
    """
    if not top:
        if len(deps) != 1:
            fail("top must be provided unless there is exactly one explicit dependency")
        top = str(deps[0]).split(":")[-1].split("/")[-1]

    synth_defines = defines
    synth_deps = deps
    if gate_library:
        synth_defines = defines + ["BR_PPA_SYNTHESIS"]
        synth_deps = deps + [gate_library]
        if structured_gate_library and top != "br_mux_bin_structured_gates":
            synth_deps.append(structured_gate_library)

    # Both profiles intentionally share a base name. The sweep appends the
    # tool and library name, producing distinct nolib and asap7_rvt_tt targets.
    verilog_yosys_synth_suite(
        name = name,
        defines = synth_defines,
        deps = synth_deps,
        sandbox_tags = tags + ["ppa-synth-generic", "ppa-synth-sandbox"],
        tags = tags + ["ppa-synth", "ppa-synth-generic"],
        top = top,
        **kwargs
    )
    asap7_rvt_tt_yosys_synth_suite(
        name = name,
        defines = synth_defines,
        deps = synth_deps,
        tags = tags,
        top = top,
        **kwargs
    )

def br_verilog_fpv_test_tools_suite(name, tools = {}, **kwargs):
    """Wraps br_verilog_fpv_test_suite with multiple formal tools.

    Args:
        name (str): The base name of the test suite.
        tools (dict[str, label]): formal tools to use and their corresponding custom tcl body files.
        **kwargs: Additional keyword arguments passed to br_verilog_fpv_test_suite.
    """

    for tool, custom_tcl_body in tools.items():
        if custom_tcl_body:
            kwargs["custom_tcl_body"] = custom_tcl_body
        br_verilog_fpv_test_suite(
            name = name + "_" + tool,
            tool = tool,
            **kwargs
        )

def br_verilog_fpv_test_suite(**kwargs):
    """Wraps verilog_fpv_test_suite with Bedrock-internal settings. Not intended to be called by Bedrock users.

    The define set is fixed for every generated FPV test and sandbox:
    * `BR_ASSERT_ON` enables assertion macros.
    * `BR_ENABLE_IMPL_CHECKS` enables Bedrock implementation checks.
    * `BR_ENABLE_FPV` enables FPV-only assertion wrappers.
    * `BR_DISABLE_FINAL_CHECKS` suppresses simulation-only final blocks, which formal tools ignore.
    * `BR_DISABLE_ASSERT_IMM` suppresses immediate/combinational checks. Formal assumptions constrain sampled
      clock edges and cannot reliably prevent between-edge immediate checks from firing.

    Args:
        **kwargs: Additional keyword arguments passed to verilog_fpv_test_suite. Do not pass defines.
    """

    if "defines" in kwargs:
        fail("Do not pass defines to br_verilog_fpv_test_suite. They are hard-coded in the macro.")

    verilog_fpv_test_suite(
        defines = [
            "BR_ASSERT_ON",
            "BR_ENABLE_IMPL_CHECKS",
            "BR_DISABLE_FINAL_CHECKS",
            "BR_ENABLE_FPV",
            "BR_DISABLE_ASSERT_IMM",
        ],
        **kwargs
    )
