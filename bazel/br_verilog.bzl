# SPDX-License-Identifier: Apache-2.0

"""Bedrock-internal Verilog rules for Bazel."""

load("//bazel:verilog.bzl", "verilog_elab_and_lint_test_suite", "verilog_fpv_test_suite", "verilog_sim_test_suite")

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

def br_verilog_sim_test_tools_suite(name, tools = [], **kwargs):
    """Wraps br_verilog_sim_test_suite with multiple simulation tools.

    Args:
        name (str): The base name of the test suite.
        tools (list of strings): simulator tools to use.
        **kwargs: Additional keyword arguments passed to br_verilog_sim_test_suite.
    """

    for tool in tools:
        br_verilog_sim_test_suite(
            name = name + "_" + tool,
            tool = tool,
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
