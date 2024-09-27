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

"""Verible lint and format test rules for Bazel."""

# TODO(mgottscho): The lint and format rules here are not the ideal solution.
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

def _verible_lint_test_impl(ctx):
    input_files = [src.path for src in ctx.files.srcs]

    args = ["--ruleset=default"]

    executable_file = ctx.actions.declare_file(ctx.label.name + ".sh")
    cmd = " ".join([ctx.attr.tool] + args + input_files)
    runfiles = ctx.runfiles(files = getattr(ctx.files, "srcs", []))

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

    return DefaultInfo(
        runfiles = runfiles,
        files = depset(direct = [executable_file]),
        executable = executable_file,
    )

verible_lint_test = rule(
    doc = "Tests that the given source files don't require Verible lint fixes.",
    implementation = _verible_lint_test_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "tool": attr.string(default = "verible-verilog-lint"),
    },
    test = True,
)

def _verible_format_test_impl(ctx):
    input_files = [src.path for src in ctx.files.srcs]

    args = ["--verify=true"]

    executable_file = ctx.actions.declare_file(ctx.label.name + ".sh")
    cmd = " ".join([ctx.attr.tool] + args + input_files)
    runfiles = ctx.runfiles(files = getattr(ctx.files, "srcs", []))

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

    return DefaultInfo(
        runfiles = runfiles,
        files = depset(direct = [executable_file]),
        executable = executable_file,
    )

verible_format_test = rule(
    doc = "Tests that the given source files don't require Verible formatting changes.",
    implementation = _verible_format_test_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "tool": attr.string(default = "verible-verilog-format"),
    },
    test = True,
)

def verible_test(name, srcs, lint_tool = "verible-verilog-lint", format_tool = "verible-verilog-format"):
    """Expands to a pair of test targets that check for Verible lint and formatting issues."""
    if not name.endswith("_verible_test"):
        fail("verible_test target names must end with '_verible_test'")

    name = name.rstrip("_verible_test")

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
