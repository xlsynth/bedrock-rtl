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

"""Verilog elaboration test rules for Bazel."""

load("@rules_hdl//verilog:providers.bzl", "VerilogInfo")

def _check_verilog_info_provider(iterable):
    """Check that all items in an iterable have the VerilogInfo provider; fails otherwise."""
    for item in iterable:
        if VerilogInfo not in item:
            fail("Label '{}' does not have the VerilogInfo provider. " +
                 "This probably means you accidentally provided a label that didn't come " +
                 "from a verilog_library target. ".format(item.label))

def _get_transitive_srcs(ctx):
    """Returns a depset of all Verilog source files in the transitive closure of the deps attribute."""
    _check_verilog_info_provider(ctx.attr.deps)
    transitive_depset = depset(
        [],
        transitive = [dep[VerilogInfo].dag for dep in ctx.attr.deps],
    )
    transitive_srcs = [
        verilog_info_struct.srcs
        for verilog_info_struct in transitive_depset.to_list()
    ]
    return depset([src for sub_tuple in transitive_srcs for src in sub_tuple])

def _get_transitive_hdrs(ctx):
    """Returns a depset of all Verilog header files in the transitive closure of the deps attribute."""
    _check_verilog_info_provider(ctx.attr.deps)
    transitive_depset = depset(
        [],
        transitive = [dep[VerilogInfo].dag for dep in ctx.attr.deps],
    )
    transitive_hdrs = [
        verilog_info_struct.hdrs
        for verilog_info_struct in transitive_depset.to_list()
    ]
    return depset([src for sub_tuple in transitive_hdrs for src in sub_tuple])

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
    srcs = ctx.files.srcs + _get_transitive_srcs(ctx).to_list()
    hdrs = ctx.files.hdrs + _get_transitive_hdrs(ctx).to_list()

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
