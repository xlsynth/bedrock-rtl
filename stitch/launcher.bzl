# SPDX-License-Identifier: Apache-2.0

"""Launcher rule for tools that need the XLS shared library at runtime."""

def _xls_dso_launcher_impl(ctx):
    executable = ctx.actions.declare_file(ctx.label.name + ".sh")
    dso = ctx.file.xls_dso
    binary = ctx.executable.binary

    ctx.actions.write(
        output = executable,
        is_executable = True,
        content = """#!/usr/bin/env bash
set -euo pipefail

export LD_LIBRARY_PATH="${{PWD}}/{dso_dir}:${{LD_LIBRARY_PATH:-}}"
exec "${{PWD}}/{binary_path}" "$@"
""".format(
            binary_path = binary.path,
            dso_dir = dso.dirname,
        ),
    )

    runfiles = ctx.runfiles(files = [binary, dso])
    runfiles = runfiles.merge(ctx.attr.binary[DefaultInfo].default_runfiles)
    runfiles = runfiles.merge(ctx.attr.xls_dso[DefaultInfo].default_runfiles)

    return [DefaultInfo(
        executable = executable,
        files = depset([executable, binary, dso]),
        runfiles = runfiles,
    )]

xls_dso_launcher = rule(
    implementation = _xls_dso_launcher_impl,
    executable = True,
    attrs = {
        "binary": attr.label(
            executable = True,
            cfg = "exec",
            mandatory = True,
        ),
        "xls_dso": attr.label(
            allow_single_file = True,
            mandatory = True,
        ),
    },
)
