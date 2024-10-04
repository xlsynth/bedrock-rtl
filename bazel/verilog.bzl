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
            "exec " + cmd,
            "exit 0",
        ]),
        is_executable = True,
    )
    return executable_file

def _verilog_elab_test_impl(ctx):
    """Implementation of the verilog_elab_test rule."""
    srcs = ctx.files.srcs + _get_transitive(ctx=ctx, srcs_not_hdrs=True).to_list()
    hdrs = ctx.files.hdrs + _get_transitive(ctx=ctx, srcs_not_hdrs=False).to_list()

    src_files = [src.path for src in srcs]
    hdr_files = [hdr.path for hdr in hdrs]

    args = ["--hdr=" + hdr for hdr in hdr_files]
    args.append("--top=" + ctx.attr.top)

    # TODO(mgottscho): Gross. Use hermetic python?
    cmd = " ".join(["python3.12"] + [ctx.attr.tool.files.to_list()[0].path] + args + src_files)

    runfiles = ctx.runfiles(files = srcs + hdrs + ctx.files.tool)
    executable_file = _write_executable_shell_script(
        ctx = ctx,
        filename = ctx.label.name + ".sh",
        cmd = cmd
    )

    return DefaultInfo(
        runfiles = runfiles,
        files = depset(direct = [executable_file]),
        executable = executable_file,
    )

def _verilog_lint_test_impl(ctx):
    """Implementation of the verilog_lint_test rule."""
    input_files = _get_transitive(ctx=ctx, srcs_not_hdrs=True).to_list() + _get_transitive(ctx=ctx, srcs_not_hdrs=False).to_list()
    cmd = " ".join(["python3.12"] + [ctx.attr.tool.files.to_list()[0].path] + [file.path for file in input_files])
    runfiles = ctx.runfiles(files = input_files + ctx.files.tool)
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

def _verible_impl(ctx):
    """Implementation of the verible_lint_test and verible_format_test rules."""
    srcs = ctx.files.srcs + _get_transitive(ctx=ctx, srcs_not_hdrs=True).to_list()
    hdrs = _get_transitive(ctx=ctx, srcs_not_hdrs=False).to_list()
    src_files = [src.path for src in srcs]
    hdr_files = [hdr.path for hdr in hdrs]
    input_files = src_files + hdr_files
    cmd = " ".join([ctx.attr.tool] + ctx.attr.tool_args + input_files)
    runfiles = ctx.runfiles(files = getattr(ctx.files, "srcs", []))
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

verilog_elab_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design elaborates.",
    implementation = _verilog_elab_test_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".v", ".sv"]),
        "hdrs": attr.label_list(allow_files = [".vh", ".svh"]),
        "deps": attr.label_list(allow_files=False),
        "top": attr.string(),
        "tool": attr.label(
            allow_single_file=True,
            default = "//bazel:verilog_elab_test.py",
        ),
    },
    test = True,
)

verilog_lint_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design passes a set of static lint checks.",
    implementation = _verilog_lint_test_impl,
    attrs = {
        "deps": attr.label_list(allow_files=False),
        "tool": attr.label(
            allow_single_file=True,
            default = "//bazel:verilog_lint_test.py",
        ),
    },
    test = True,
)

# TODO(mgottscho): The verible lint and format rules here are not the ideal solution.
# We'd prefer to only run the linter and formatter on the changed lines in a
# git diff so that we can change the lint/format rules over time (if needed)
# and have the tests gradually ratchet over the codebase. I'm fine with this
# non-ideal solution for now, though, since we're setting this up on a fresh
# codebase and moving fast.
#
# The ideal solution would probably look like this:
#
# bazel run //:verible-format      # Test only changed lines
# bazel run //:verible-format-fix  # Test and fix changed lines in-place
#
# bazel run //:verible-format -- <file1.sv> <file2.sv>  # Run on specific files
# bazel run //:verible-format-fix -- <file1.sv> <file2.sv>  # Fix specific files
#
# bazel run //:verible-format -- --all      # Test all lines
# bazel run //:verible-format-fix -- --all  # Fix all lines
verible_lint_test = rule(
    doc = "Tests that the given source files don't have syntax errors or Verible lint errors.",
    implementation = _verible_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".v", ".sv", ".svh"]),
        "deps": attr.label_list(allow_files=False),
        # By default, expect to find the tool in the system $PATH.
        # TODO(mgottscho): It would be better to do this hermetically.
        "tool": attr.string(default = "verible-verilog-lint"),
        "tool_args": attr.string_list(default = ["--ruleset=default"]),
    },
    test = True,
)

verible_format_test = rule(
    doc = "Tests that the given source files don't have syntax errors or Verible formatting errors.",
    implementation = _verible_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".v", ".sv", ".svh"]),
        "deps": attr.label_list(allow_files=False),
        # By default, expect to find the tool in the system $PATH.
        # TODO(mgottscho): It would be better to do this hermetically.
        "tool": attr.string(default = "verible-verilog-format"),
        "tool_args": attr.string_list(default = ["--verify=true"]),
    },
    test = True,
)

def verible_test(name, srcs, lint_tool = "verible-verilog-lint", format_tool = "verible-verilog-format"):
    """Expands to a pair of test targets that check for Verible lint and formatting issues."""
    if not name.endswith("_verible_test"):
        fail("verible_test target names must end with '_verible_test'")

    name = name.removesuffix("_verible_test")

    verible_lint_test(
        name = name + "_verible_lint_test",
        srcs = srcs,
        tool = lint_tool,
    )

    verible_format_test(
        name = name + "_verible_format_test",
        srcs = srcs,
        tool = format_tool,
    )
