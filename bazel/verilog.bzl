# Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Verilog rules for Bazel."""

load("@rules_hdl//verilog:providers.bzl", "VerilogInfo")
load("//bazel:write_placeholder_tools.bzl", "write_placeholder_verilog_test_tool")

def get_transitive(ctx, srcs_not_hdrs):
    """Returns a depset of all Verilog source or header files in the transitive closure of the deps attribute."""
    transitive_depset = depset(
        [],
        transitive = [dep[VerilogInfo].dag for dep in ctx.attr.deps],
    )
    transitive_srcs_or_hdrs = [
        verilog_info_struct.srcs if srcs_not_hdrs else verilog_info_struct.hdrs
        for verilog_info_struct in transitive_depset.to_list()
    ]
    return depset([x for sub_tuple in transitive_srcs_or_hdrs for x in sub_tuple])

def _write_executable_shell_script(ctx, filename, cmd):
    """Writes a shell script that executes the given command and returns a handle to it."""
    executable_file = ctx.actions.declare_file(filename)
    ctx.actions.write(
        output = executable_file,
        content = "\n".join([
            "#!/usr/bin/env bash",
            "set -ex",
            "pwd",
            cmd,
        ]),
        is_executable = True,
    )
    return executable_file

def _verilog_base_test_impl(ctx, subcmd, extra_args = []):
    """Shared implementation for verilog_elab_test, verilog_lint_test, and verilog_sim_test.

    Grab tool from the environment (BAZEL_VERILOG_TEST_TOOL) so that
    the user can provide their own proprietary tool implementation without
    it being hardcoded anywhere into the repo. It's not hermetic, but it's
    a decent compromise.

    Args:
        ctx: ctx for the rule
        subcmd (string): the tool subcommand to run
        extra_args (list of strings, optional): tool-specific args

    Returns:
        DefaultInfo for the rule that describes the runfiles, depset, and executable
    """
    env = ctx.configuration.default_shell_env
    if "BAZEL_VERILOG_TEST_TOOL" in env:
        tool = env.get("BAZEL_VERILOG_TEST_TOOL")
        extra_runfiles = []
    else:
        # buildifier: disable=print
        print("!! WARNING !! Environment variable BAZEL_VERILOG_TEST_TOOL is not set! Will use placeholder test tool.")
        tool_file = write_placeholder_verilog_test_tool(ctx, "placeholder_verilog_test.py")
        extra_runfiles = [tool_file]
        tool = tool_file.short_path

    srcs = get_transitive(ctx = ctx, srcs_not_hdrs = True).to_list()
    hdrs = get_transitive(ctx = ctx, srcs_not_hdrs = False).to_list()
    src_files = [src.short_path for src in srcs]
    hdr_files = [hdr.short_path for hdr in hdrs]
    top = ctx.attr.top
    if top == "":
        if (len(ctx.attr.deps) != 1):
            fail("If the top attribute is not provided, then there must be exactly one dependency.")
        top = ctx.attr.deps[0].label.name
    args = (["--hdr=" + hdr for hdr in hdr_files] +
            ["--define=" + define for define in ctx.attr.defines] +
            ["--top=" + top] +
            ["--param=" + key + "=" + value for key, value in ctx.attr.params.items()] +
            extra_args)
    cmd = " ".join([tool] + [subcmd] + args + src_files)
    runfiles = ctx.runfiles(files = srcs + hdrs + extra_runfiles)
    executable_file = _write_executable_shell_script(
        ctx = ctx,
        filename = ctx.label.name + ".sh",
        cmd = cmd,
    )
    return DefaultInfo(
        runfiles = runfiles,
        files = depset(direct = [executable_file]),
        executable = executable_file,
    )

def _verilog_elab_test_impl(ctx):
    """Implementation of the verilog_elab_test rule."""
    return _verilog_base_test_impl(
        ctx = ctx,
        subcmd = "elab",
    )

def _verilog_lint_test_impl(ctx):
    """Implementation of the verilog_lint_test rule."""
    return _verilog_base_test_impl(
        ctx = ctx,
        subcmd = "lint",
    )

def _verilog_sim_test_impl(ctx):
    """Implementation of the verilog_sim_test rule."""
    extra_args = []
    if ctx.attr.elab_only:
        extra_args.append("--elab_only")
    if ctx.attr.uvm:
        extra_args.append("--uvm")
    if ctx.attr.tool != "":
        extra_args.append("--tool=" + ctx.attr.tool)
    if ctx.attr.seed != None:
        extra_args.append("--seed=" + str(ctx.attr.seed))
    if ctx.attr.waves:
        extra_args.append("--waves")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")

    return _verilog_base_test_impl(
        ctx = ctx,
        subcmd = "sim",
        extra_args = extra_args,
    )

# Rule definitions
_verilog_elab_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design elaborates.",
    implementation = _verilog_elab_test_impl,
    attrs = {
        "deps": attr.label_list(allow_files = False, providers = [VerilogInfo], doc = "The dependencies of the test."),
        "defines": attr.string_list(doc = "Preprocessor defines to pass to the Verilog compiler."),
        "params": attr.string_dict(doc = "Verilog module parameters to set in the instantiation of the top-level module."),
        "top": attr.string(doc = "The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name."),
    },
    test = True,
)

def verilog_elab_test(tags = [], **kwargs):
    _verilog_elab_test(
        tags = tags + ["resources:verilog_elab_test_tool_licenses:1"],
        **kwargs
    )

_verilog_lint_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design passes a set of static lint checks.",
    implementation = _verilog_lint_test_impl,
    attrs = {
        "deps": attr.label_list(allow_files = False, providers = [VerilogInfo], doc = "The dependencies of the test."),
        "defines": attr.string_list(doc = "Preprocessor defines to pass to the Verilog compiler."),
        "params": attr.string_dict(doc = "Verilog module parameters to set in the instantiation of the top-level module."),
        "top": attr.string(doc = "The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name."),
    },
    test = True,
)

def verilog_lint_test(tags = [], **kwargs):
    _verilog_lint_test(
        tags = tags + ["resources:verilog_lint_test_tool_licenses:1"],
        **kwargs
    )

_verilog_sim_test = rule(
    doc = """
    Runs Verilog compilation and simulation in one command. This rule should be used for simple unit tests that do not require multi-step compilation, elaboration, and simulation.
    """,
    implementation = _verilog_sim_test_impl,
    attrs = {
        "deps": attr.label_list(
            doc = "The dependencies of the test.",
            allow_files = False,
            providers = [VerilogInfo],
        ),
        "defines": attr.string_list(
            doc = "Preprocessor defines to pass to the Verilog compiler.",
        ),
        "params": attr.string_dict(
            doc = "Verilog module parameters to set in the instantiation of the top-level module.",
        ),
        "top": attr.string(
            doc = "The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.",
        ),
        "opts": attr.string_list(
            doc = "Compile and simulation options.",
        ),
        "elab_only": attr.bool(
            doc = "Only run elaboration.",
            default = False,
        ),
        "uvm": attr.bool(
            doc = "Run UVM test.",
            default = False,
        ),
        "tool": attr.string(
            doc = "Simulator tool to use.",
        ),
        "seed": attr.int(
            doc = "Random seed to use in simulation.",
            default = 0,
        ),
        "waves": attr.bool(
            doc = "Enable waveform dumping.",
            default = False,
        ),
    },
    test = True,
)

def verilog_sim_test(tags = [], **kwargs):
    _verilog_sim_test(
        tags = tags + ["resources:verilog_sim_test_tool_licenses:1"],
        **kwargs
    )

def _cartesian_product(lists):
    """Return the cartesian product of a list of lists."""
    result = [[]]
    for pool in lists:
        result = [x + [y] for x in result for y in pool]
    return result

def _make_test_name(base_name, suffix, param_keys, combination):
    """Generate a unique test name based on a combination of parameter values."""
    parts = [base_name]
    for key, value in zip(param_keys, combination):
        parts.append("%s%s" % (key, value))
    parts.append(suffix)
    return "_".join(parts)

def verilog_elab_and_lint_test_suite(name, defines = [], params = {}, **kwargs):
    """Creates a suite of Verilog elaboration and lint tests for each combination of the provided parameters.

    Args:
        name (str): The base name for the test suite.
        defines (list): A list of defines.
        params (dict): A dictionary where keys are parameter names and values are lists of possible values for those parameters.
        **kwargs: Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.

    The function generates all possible combinations of the provided parameters and creates a verilog_elab_test
    and a verilog_lint_test for each combination. The test names are generated by appending "_elab_test" and "_lint_test"
    to the base name followed by the parameter key-values.
    """
    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = _cartesian_product(param_values_list)

    # Create a verilog_elab_test and verilog_lint_test for each combination of parameters
    for param_combination in param_combinations:
        params = dict(zip(param_keys, param_combination))
        verilog_elab_test(
            name = _make_test_name(name, "elab_test", param_keys, param_combination),
            defines = defines,
            params = params,
            **kwargs
        )
        verilog_lint_test(
            name = _make_test_name(name, "lint_test", param_keys, param_combination),
            defines = defines,
            params = params,
            **kwargs
        )
