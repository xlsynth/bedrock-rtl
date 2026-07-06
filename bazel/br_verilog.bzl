# SPDX-License-Identifier: Apache-2.0

"""Bedrock-internal Verilog rules for Bazel."""

load("//bazel:verilog.bzl", "verilog_elab_and_lint_test_suite", "verilog_fpv_test_suite", "verilog_sim_test_suite", "verilog_synth_suite")

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

def br_verilog_synth_suite(
        name,
        tool = "yosys",
        defines = ["SYNTHESIS"],
        deps = [],
        gate_library = "//gate/rtl:br_gate_mock",
        library_name = None,
        structured_gate_library = "//mux/rtl:br_mux_bin_structured_gates",
        tags = [],
        top = None,
        **kwargs):
    """Creates Bedrock logic-synthesis sweeps for representative parameter combinations.

    Args:
        name (str): Base name of the generated synthesis targets.
        tool (str): Verilog Runner synthesis plugin. Defaults to Yosys.
        defines (list[str]): Synthesis preprocessor defines.
        deps (list[label]): Verilog library dependencies.
        gate_library (label): Generic gate model used for no-PDK Yosys PPA runs.
        library_name (str or None): Target-name identifier for the PDK/library/corner. Defaults to `nolib` for
            no-Liberty synthesis and is required when a Liberty file is supplied.
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
    if tool == "yosys" and gate_library:
        synth_defines = defines + ["BR_PPA_SYNTHESIS"]
        synth_deps = deps + [gate_library]
        if structured_gate_library and top != "br_mux_bin_structured_gates":
            synth_deps.append(structured_gate_library)

    verilog_synth_suite(
        name = name,
        tool = tool,
        defines = synth_defines,
        deps = synth_deps,
        library_name = library_name,
        sandbox_tags = tags + ["ppa-synth-generic", "ppa-synth-sandbox"],
        tags = tags + ["ppa-synth", "ppa-synth-generic"],
        top = top,
        **kwargs
    )

def br_verilog_fpv_test_tools_suite(name, tools = {}, **kwargs):
    """Wraps br_verilog_fpv_test_suite with multiple formal tools.

    Args:
        name (str): The base name of the test suite.
        tools (dict[str, label|dict]): Formal tools to use. A label value is a custom control body.
            A dict value overrides suite arguments for that tool, including deps, top, opts,
            custom_control_header, custom_control_body, custom_tcl_header, and custom_tcl_body.
        **kwargs: Additional keyword arguments passed to br_verilog_fpv_test_suite.
    """

    for tool, tool_config in tools.items():
        tool_kwargs = dict(kwargs)
        if type(tool_config) == "dict":
            tool_kwargs.update(tool_config)
        elif type(tool_config) in ["string", "Label"]:
            if tool_config:
                tool_kwargs["custom_control_body"] = tool_config
        else:
            fail("FPV tool configuration for {} must be a string, Label, or dict".format(tool))
        br_verilog_fpv_test_suite(
            name = name + "_" + tool,
            tool = tool,
            **tool_kwargs
        )

def br_verilog_fpv_test_suite(tool, **kwargs):
    """Wraps verilog_fpv_test_suite with Bedrock-internal settings. Not intended to be called by Bedrock users.

    The common define set enables Bedrock assertions and FPV checks:
    * `BR_ASSERT_ON` enables assertion macros.
    * `BR_ENABLE_IMPL_CHECKS` enables Bedrock implementation checks.
    * `BR_ENABLE_FPV` enables FPV-only assertion wrappers.
    * `BR_DISABLE_FINAL_CHECKS` suppresses simulation-only final blocks, which formal tools ignore.

    Proprietary formal tools additionally define `BR_DISABLE_ASSERT_IMM` because their assumptions constrain
    sampled clock edges and cannot reliably prevent between-edge immediate checks from firing. SBY instead defines
    `BR_YOSYS_SBY` to suppress unsupported concurrent SVA while leaving the immediate/combinational FPV macros
    enabled for its tool-compatible harnesses.

    Args:
        tool (str): The formal tool to use.
        **kwargs: Additional keyword arguments passed to verilog_fpv_test_suite. Do not pass defines.
    """

    if "defines" in kwargs:
        fail("Do not pass defines to br_verilog_fpv_test_suite. They are hard-coded in the macro.")

    defines = [
        "BR_ASSERT_ON",
        "BR_ENABLE_IMPL_CHECKS",
        "BR_DISABLE_FINAL_CHECKS",
        "BR_ENABLE_FPV",
    ]
    if tool == "sby":
        defines.append("BR_YOSYS_SBY")
    else:
        defines.append("BR_DISABLE_ASSERT_IMM")

    verilog_fpv_test_suite(
        defines = defines,
        tool = tool,
        **kwargs
    )
