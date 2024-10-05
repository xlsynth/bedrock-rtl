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
load(
    "//bazel:write_placeholder_tools.bzl",
    "write_placeholder_verilog_elab_test_tool",
    "write_placeholder_verilog_lint_test_tool",
)

def _check_verilog_info_provider(iterable):
    """Check that all items in an iterable have the VerilogInfo provider; fails otherwise."""
    for item in iterable:
        if VerilogInfo not in item:
            fail("Label '{}' does not have the VerilogInfo provider. " +
                 "This probably means you accidentally provided a label that didn't come " +
                 "from a verilog_library target. ".format(item.label))

def _get_transitive(ctx, srcs_not_hdrs):
    """Returns a depset of all Verilog source or header files in the transitive closure of the deps attribute."""
    _check_verilog_info_provider(ctx.attr.deps)
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
            "set -e",
            "echo 'Running command:'",
            "echo {}".format(cmd),
            cmd,
            "exit 0",
        ]),
        is_executable = True,
    )
    return executable_file

def _verilog_base_test_impl(ctx, tool, extra_args = [], extra_runfiles = []):
    srcs = _get_transitive(ctx = ctx, srcs_not_hdrs = True).to_list()
    hdrs = _get_transitive(ctx = ctx, srcs_not_hdrs = False).to_list()
    src_files = [src.path for src in srcs]
    hdr_files = [hdr.path for hdr in hdrs]
    args = ["--hdr=" + hdr for hdr in hdr_files] + extra_args
    cmd = " ".join([tool] + args + src_files)
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
    """Implementation of the verilog_elab_test rule.

    Grab tool from the environment (BAZEL_VERILOG_ELAB_TEST_TOOL) so that
    the user can provide their own proprietary tool implementation without
    it being hardcoded anywhere into the repo. It's not hermetic, but it's
    a decent compromise.
    """
    env = ctx.configuration.default_shell_env
    if "BAZEL_VERILOG_ELAB_TEST_TOOL" in env:
        tool = ctx.configuration.default_shell_env.get("BAZEL_VERILOG_ELAB_TEST_TOOL")
        extra_runfiles = []
    else:
        # buildifier: disable=print
        print("!! WARNING !! Environment variable BAZEL_VERILOG_ELAB_TEST_TOOL is not set! Will use placeholder test tool.")
        tool_file = write_placeholder_verilog_elab_test_tool(ctx)
        extra_runfiles = [tool_file]
        tool = tool_file.short_path
    return _verilog_base_test_impl(
        ctx = ctx,
        tool = tool,
        extra_args = ["--top=" + ctx.attr.top],
        extra_runfiles = extra_runfiles,
    )

def _verilog_lint_test_impl(ctx):
    """Implementation of the verilog_lint_test rule.

    Grab tool from the environment (BAZEL_VERILOG_LINT_TEST_TOOL) so that
    the user can provide their own proprietary tool implementation without
    it being hardcoded anywhere into the repo. It's not hermetic, but it's
    a decent compromise.
    """
    env = ctx.configuration.default_shell_env
    if "BAZEL_VERILOG_LINT_TEST_TOOL" in env:
        tool = ctx.configuration.default_shell_env.get("BAZEL_VERILOG_LINT_TEST_TOOL")
        extra_runfiles = []
    else:
        # buildifier: disable=print
        print("!! WARNING !! Environment variable BAZEL_VERILOG_LINT_TEST_TOOL is not set! Will use placeholder test tool.")
        tool_file = write_placeholder_verilog_lint_test_tool(ctx)
        extra_runfiles = [tool_file]
        tool = tool_file.short_path
    return _verilog_base_test_impl(
        ctx = ctx,
        tool = tool,
        extra_runfiles = extra_runfiles,
    )

_verilog_elab_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design elaborates.",
    implementation = _verilog_elab_test_impl,
    attrs = {
        "deps": attr.label_list(allow_files = False),
        "top": attr.string(),
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
        "deps": attr.label_list(allow_files = False),
    },
    test = True,
)

def verilog_lint_test(tags = [], **kwargs):
    _verilog_lint_test(
        tags = tags + ["resources:verilog_lint_test_tool_licenses:1"],
        **kwargs
    )
