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

def _verible_lint_test_impl(ctx):
    input_files = [src.path for src in ctx.files.srcs]

    args = [
        "--rules=" + ctx.attr.rules,
        "--rules_config=" + ctx.attr.rules_config,
        "--ruleset=" + ctx.attr.ruleset,
        "--waiver_files=" + ctx.attr.waiver_files,
        "--show_diagnostic_context=" + ctx.attr.show_diagnostic_context,
    ]

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
    doc = "Runs the Verible verilog linter on the given source files.",
    implementation = _verible_lint_test_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "rules": attr.string(default = ""),
        "rules_config": attr.string(default = ""),
        "ruleset": attr.string(default = "default"),
        "waiver_files": attr.string(default = ""),
        "show_diagnostic_context": attr.string(default = "false"),
        "tool": attr.string(default = "verible-verilog-lint"),
    },
    test = True,
)
