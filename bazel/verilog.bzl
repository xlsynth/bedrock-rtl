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
load("//bazel:write_placeholder_verilog_runner_py.bzl", "write_placeholder_verilog_runner_tool")

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
    content = [
        "#!/usr/bin/env bash",
        "set -ex",
        "pwd",
        cmd,
        "",
    ]
    ctx.actions.write(
        output = executable_file,
        content = "\n".join(content),
        is_executable = True,
    )
    return executable_file

def _verilog_base_impl(ctx, subcmd, test = True, extra_args = [], extra_runfiles = []):
    """Shared implementation for rule_verilog_elab_test, rule_verilog_lint_test, rule_verilog_sim_test, and rule_verilog_fpv_test.

    Grab tool from the environment (BAZEL_VERILOG_RUNNER_TOOL) so that
    the user can provide their own proprietary tool implementation without
    it being hardcoded anywhere into the repo. It's not hermetic, but it's
    a decent compromise.

    Args:
        ctx: ctx for the rule
        subcmd (string): the tool subcommand to run
        test (bool, optional): whether the rule is a test; if not, then generate a tarball sandbox
        extra_args (list of strings, optional): tool-specific args
        extra_runfiles (list of files, optional): tool-specific files

    Returns:
        DefaultInfo for the rule that describes the runfiles, depset, and executable
    """
    env = ctx.configuration.default_shell_env
    if "BAZEL_VERILOG_RUNNER_TOOL" in env:
        wrapper_tool = env.get("BAZEL_VERILOG_RUNNER_TOOL")
    else:
        # buildifier: disable=print
        print("!! WARNING !! Environment variable BAZEL_VERILOG_RUNNER_TOOL is not set! Will use placeholder runner tool.")
        wrapper_tool_file = write_placeholder_verilog_runner_tool(ctx, "placeholder_verilog_runner.py")
        extra_runfiles.append(wrapper_tool_file)
        wrapper_tool = wrapper_tool_file.short_path

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
            ["--param=" + key + "=" + value for key, value in ctx.attr.params.items()])
    tcl = ctx.label.name + ".tcl"
    script = ctx.label.name + ".sh"
    log = ctx.label.name + ".log"

    args.append("--tcl=" + tcl)
    args.append("--script=" + script)
    args.append("--log=" + log)
    if ctx.attr.tool:
        args.append("--tool='" + ctx.attr.tool + "'")
    if not test:
        args.append("--dry-run")
    args += extra_args
    cmd = " ".join([wrapper_tool] + [subcmd] + args + src_files)
    runfiles = ctx.runfiles(files = srcs + hdrs + extra_runfiles)
    if test:
        runner = ctx.label.name + "_runner.sh"
        runner_executable_file = _write_executable_shell_script(
            ctx = ctx,
            filename = runner,
            cmd = cmd,
        )
        return DefaultInfo(
            runfiles = runfiles,
            files = depset(direct = [runner_executable_file]),
            executable = runner_executable_file,
        )

    else:
        generator = ctx.label.name + "_generator.sh"
        generator_executable_file = _write_executable_shell_script(
            ctx = ctx,
            filename = generator,
            cmd = cmd,
        )
        generator_inputs = srcs + hdrs + extra_runfiles + [generator_executable_file]
        generator_outputs = [tcl, script]

        # Run generator and generate tarball
        tar_inputs = []
        for f in srcs + hdrs + extra_runfiles:
            tar_inputs.append(f.path)
        for f in generator_outputs:
            tar_inputs.append(f)

        generator_cmd = [
            "source",
            generator_executable_file.path,
        ]
        tar_cmd = [
            "tar --dereference -czf",
            ctx.outputs.out.path,
        ] + tar_inputs
        tar_cmd = " ".join(tar_cmd)

        generator_cmd = " ".join(generator_cmd)

        command = " && ".join([generator_cmd, tar_cmd])

        ctx.actions.run_shell(
            inputs = generator_inputs,
            outputs = [ctx.outputs.out],
            command = command,
        )

        return DefaultInfo(
            files = depset(direct = [ctx.outputs.out]),
        )

def _verilog_elab_test_impl(ctx):
    """Implementation of the verilog_elab_test rule."""
    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "elab",
    )

def _verilog_lint_test_impl(ctx):
    """Implementation of the verilog_lint_test rule."""
    extra_args = []
    extra_runfiles = []
    if ctx.attr.policy:
        extra_args.append("--policy=" + ctx.attr.policy.files.to_list()[0].short_path)
        extra_runfiles += ctx.files.policy
    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "lint",
        extra_args = extra_args,
        extra_runfiles = extra_runfiles,
    )

def _verilog_sim_test_impl(ctx):
    """Implementation of the verilog_sim_test rule."""
    extra_args = []
    if ctx.attr.tool:
        extra_args.append("--filelist=sim_" + ctx.attr.tool + ".f")
    else:
        extra_args.append("--filelist=sim.f")
    if ctx.attr.elab_only:
        extra_args.append("--elab_only")
    if ctx.attr.uvm:
        extra_args.append("--uvm")
    extra_args.append("--seed='" + str(ctx.attr.seed) + "'")
    if ctx.attr.waves:
        extra_args.append("--waves")
    if len(ctx.attr.opts) > 0 and ctx.attr.tool == "":
        fail("If opts are provided, then tool must also be set.")

    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "sim",
        extra_args = extra_args,
    )

def _verilog_fpv_test_impl(ctx):
    """Implementation of the verilog_fpv_test rule."""
    extra_args = []
    if ctx.attr.elab_only:
        extra_args.append("--elab_only")
    if len(ctx.attr.opts) > 0 and ctx.attr.tool == "":
        fail("If opts are provided, then tool must also be set.")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "fpv",
        extra_args = extra_args,
    )

def _verilog_sandbox_impl(ctx):
    """Implementation of the verilog_sandbox rule."""
    extra_args = []
    if len(ctx.attr.opts) > 0 and ctx.attr.tool == "":
        fail("If opts are provided, then tool must also be set.")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")

    if ctx.attr.kind == "sim":
        if ctx.attr.tool:
            extra_args.append("--filelist=sim_" + ctx.attr.tool + ".f")
        else:
            extra_args.append("--filelist=sim.f")

    # Check if the filename ends with '.tar.gz'
    if not ctx.outputs.out.basename.endswith(".tar.gz"):
        fail("The 'out' attribute must be a file ending with '.tar.gz', but got '{}'.".format(ctx.outputs.out.basename))

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = ctx.attr.kind,
        test = False,
        extra_args = extra_args,
    )

# Rule definitions
rule_verilog_elab_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design elaborates. Needs BAZEL_VERILOG_RUNNER_TOOL environment variable to be set correctly.",
    implementation = _verilog_elab_test_impl,
    attrs = {
        "deps": attr.label_list(allow_files = False, providers = [VerilogInfo], doc = "The dependencies of the test."),
        "defines": attr.string_list(doc = "Preprocessor defines to pass to the Verilog compiler."),
        "params": attr.string_dict(doc = "Verilog module parameters to set in the instantiation of the top-level module."),
        "top": attr.string(doc = "The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name."),
        "tool": attr.string(doc = "Elaboration tool to use. If not provided, default is decided by the BAZEL_VERILOG_RUNNER_TOOL implementation."),
    },
    test = True,
)

def verilog_elab_test(tags = [], **kwargs):
    """Wraps rule_verilog_elab_test with a resource tag: 'resources:verilog_elab_test_tool_licenses:1.'

    Useful for having Bazel self-throttle test actions that require a finite number of elab tool licenses.
    """
    rule_verilog_elab_test(
        tags = tags + [
            "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
            "resources:verilog_elab_test_tool_licenses:1",
        ],
        **kwargs
    )

rule_verilog_lint_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design passes a set of static lint checks. Needs BAZEL_VERILOG_RUNNER_TOOL environment variable to be set correctly.",
    implementation = _verilog_lint_test_impl,
    attrs = {
        "deps": attr.label_list(
            allow_files = False,
            providers = [VerilogInfo],
            doc = "The dependencies of the test.",
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
        "policy": attr.label(
            allow_files = True,
            doc = "The lint policy file to use. If not provided, then the default tool policy is used (typically provided through an environment variable).",
        ),
        "tool": attr.string(doc = "Lint tool to use. If not provided, default is decided by the BAZEL_VERILOG_RUNNER_TOOL implementation."),
    },
    test = True,
)

def verilog_lint_test(tags = [], **kwargs):
    """Wraps rule_verilog_lint_test with a resource tag: 'resources:verilog_lint_test_tool_licenses:1.'

    Useful for having Bazel self-throttle test actions that require a finite number of lint tool licenses.
    """
    rule_verilog_lint_test(
        tags = tags + [
            "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
            "resources:verilog_lint_test_tool_licenses:1",
        ],
        **kwargs
    )

rule_verilog_sim_test = rule(
    doc = """
    Runs Verilog/SystemVerilog compilation and simulation in one command. This rule should be used for simple unit tests that do not require multi-step compilation, elaboration, and simulation. Needs BAZEL_VERILOG_RUNNER_TOOL environment variable to be set correctly.
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
            doc = "Tool-specific options not covered by other arguments. If provided, then 'tool' must also be set.",
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
            doc = "Simulator tool to use. If not provided, default is decided by the BAZEL_VERILOG_RUNNER_TOOL implementation.",
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
    """Wraps rule_verilog_sim_test with a resource tag: 'resources:verilog_sim_test_tool_licenses:1.'

    Useful for having Bazel self-throttle test actions that require a finite number of simulator tool licenses.
    """
    rule_verilog_sim_test(
        tags = tags + [
            "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
            "resources:verilog_sim_test_tool_licenses:1",
        ],
        **kwargs
    )

rule_verilog_fpv_test = rule(
    doc = """
    Runs Verilog/SystemVerilog compilation and formal verification in one command. This rule should be used for simple formal unit tests. Needs BAZEL_VERILOG_RUNNER_TOOL environment variable to be set correctly.
    """,
    implementation = _verilog_fpv_test_impl,
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
            doc = "Tool-specific options not covered by other arguments. If provided, then 'tool' must also be set.",
        ),
        "elab_only": attr.bool(
            doc = "Only run elaboration.",
            default = False,
        ),
        "tool": attr.string(
            doc = "Formal tool to use. If not provided, default is decided by the BAZEL_VERILOG_RUNNER_TOOL implementation.",
        ),
    },
    test = True,
)

def verilog_fpv_test(tags = [], **kwargs):
    """Wraps rule_verilog_fpv_test with a resource tag: 'resources:verilog_fpv_test_tool_licenses:1.'

    Useful for having Bazel self-throttle test actions that require a finite number of formal tool licenses.
    """
    rule_verilog_fpv_test(
        tags = tags + [
            "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
            "resources:verilog_fpv_test_tool_licenses:1",
        ],
        **kwargs
    )

rule_verilog_sandbox = rule(
    doc = "Writes files and run scripts into a tarball for independent execution outside of Bazel.",
    implementation = _verilog_sandbox_impl,
    attrs = {
        "deps": attr.label_list(
            doc = "The Verilog dependencies of the sandbox.",
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
            doc = "Tool-specific options not covered by other arguments. If provided, then 'tool' must also be set.",
        ),
        "kind": attr.string(
            doc = "The kind of sandbox to create: [elab, lint, sim, fpv].",
            values = ["elab", "lint", "sim", "fpv"],
            mandatory = True,
        ),
        "tool": attr.string(
            doc = "Tool to use. If not provided, default is decided by the BAZEL_VERILOG_RUNNER_TOOL implementation.",
        ),
    },
    outputs = {
        "out": "%{name}.tar.gz",
    },
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

    The function generates all possible combinations of the provided parameters and creates a verilog_elab_test
    and a verilog_lint_test for each combination. The test names are generated by appending "_elab_test" and "_lint_test"
    to the base name followed by the parameter key-values.

    Args:
        name (str): The base name for the test suite.
        defines (list): A list of defines.
        params (dict): A dictionary where keys are parameter names and values are lists of possible values for those parameters.
        **kwargs: Additional common keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.
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

def verilog_fpv_test_suite(name, defines = [], params = {}, **kwargs):
    """Creates a suite of Verilog fpv tests for each combination of the provided parameters.

    The function generates all possible combinations of the provided parameters and creates a verilog_fpv_test
    for each combination. The test names are generated by appending "_fpv_test"
    to the base name followed by the parameter key-values.

    Args:
        name (str): The base name for the test suite.
        defines (list): A list of defines.
        params (dict): A dictionary where keys are parameter names and values are lists of possible values for those parameters.
        **kwargs: Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.
    """
    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = _cartesian_product(param_values_list)

    # Create a verilog_fpv_test for each combination of parameters
    for param_combination in param_combinations:
        params = dict(zip(param_keys, param_combination))
        verilog_fpv_test(
            name = _make_test_name(name, "fpv_test", param_keys, param_combination),
            defines = defines,
            params = params,
            **kwargs
        )
