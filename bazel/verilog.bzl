# Copyright 2024-2025 The Bedrock-RTL Authors
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

def _write_executable_shell_script(ctx, executable_file, cmd, verbose = True, env_exports = None):
    """Writes a shell script that executes the given command and returns a handle to it."""
    lines = [
        "#!/usr/bin/env bash",
        "set -ex" if verbose else "set -e",
    ]

    # Insert environment variable exports if provided
    if env_exports:
        for key, value in env_exports.items():
            lines.append("export {}={}".format(key, value))
    if verbose:
        lines.append("pwd")
    lines.append(cmd)
    lines.append("")
    ctx.actions.write(
        output = executable_file,
        content = "\n".join(lines),
        is_executable = True,
    )

def _verilog_base_impl(ctx, subcmd, test = True, extra_args = [], extra_runfiles = []):
    """Shared implementation for rule_verilog_elab_test, rule_verilog_lint_test, rule_verilog_sim_test, and rule_verilog_fpv_test.

    Args:
        ctx: ctx for the rule
        subcmd (string): the tool subcommand to run
        test (bool, optional): whether the rule is a test; if not, then generate a tarball sandbox
        extra_args (list of strings, optional): tool-specific args
        extra_runfiles (list of files, optional): tool-specific files

    Returns:
        DefaultInfo for the rule that describes the runfiles, depset, and executable
    """
    runfiles = []
    runfiles += ctx.files.verilog_runner_tool
    runfiles += ctx.files.verilog_runner_plugins
    srcs = get_transitive(ctx = ctx, srcs_not_hdrs = True).to_list()
    hdrs = get_transitive(ctx = ctx, srcs_not_hdrs = False).to_list()
    if test:
        src_files = [src.short_path for src in srcs]
        hdr_files = [hdr.short_path for hdr in hdrs]
    else:
        src_files = [src.path for src in srcs]
        hdr_files = [hdr.path for hdr in hdrs]
    top = ctx.attr.top
    if top == "":
        if (len(ctx.attr.deps) != 1):
            fail("If the top attribute is not provided, then there must be exactly one dependency.")
        top = ctx.attr.deps[0].label.name
    args = (["--hdr=" + hdr for hdr in hdr_files] +
            ["--define=" + define for define in ctx.attr.defines] +
            ["--top=" + top] +
            ["--param=" + key + "=" + value for key, value in ctx.attr.params.items()])
    filelist = ctx.label.name + ".f"
    tcl = ctx.label.name + ".tcl"
    script = ctx.label.name + ".sh"
    log = ctx.label.name + ".log"
    args.append("--filelist=" + filelist)
    args.append("--tcl=" + tcl)
    args.append("--script=" + script)
    args.append("--log=" + log)
    if ctx.attr.tool:
        args.append("--tool='" + ctx.attr.tool + "'")
    if not test:
        args.append("--dry-run")
    if ctx.attr.custom_tcl_header:
        if test:
            args.append("--custom_tcl_header=" + ctx.files.custom_tcl_header[0].short_path)
        else:
            args.append("--custom_tcl_header=" + ctx.files.custom_tcl_header[0].path)
        runfiles += ctx.files.custom_tcl_header
    if ctx.attr.custom_tcl_body:
        if test:
            args.append("--custom_tcl_body=" + ctx.files.custom_tcl_body[0].short_path)
        else:
            args.append("--custom_tcl_body=" + ctx.files.custom_tcl_body[0].path)
        runfiles += ctx.files.custom_tcl_body
    args += extra_args

    # TODO: This is a hack. We should use the py_binary target directly, but I'm not sure how to get the environment
    # to work correctly when we wrap the py_binary in a shell script that gets invoked later.
    if test:
        runner_path = ctx.files.verilog_runner_tool[0].short_path
    else:
        runner_path = ctx.files.verilog_runner_tool[0].path
    plugin_paths = []
    for plugin in ctx.files.verilog_runner_plugins:
        if plugin.dirname not in plugin_paths:
            plugin_paths.append(plugin.dirname)
    verilog_runner_plugin_paths = ":".join(plugin_paths)
    env_exports = {
        "VERILOG_RUNNER_PLUGIN_PATH": "${VERILOG_RUNNER_PLUGIN_PATH}:" + verilog_runner_plugin_paths,
    }

    verilog_runner_cmd = " ".join(["python3"] + [runner_path] + [subcmd] + args + src_files)
    verilog_runner_runfiles = ctx.runfiles(files = srcs + hdrs + runfiles + extra_runfiles)
    if test:
        runner = ctx.label.name + "_runner.sh"
        runner_executable_file = ctx.actions.declare_file(runner)
        _write_executable_shell_script(
            ctx = ctx,
            executable_file = runner_executable_file,
            cmd = verilog_runner_cmd,
            env_exports = env_exports,
        )
        return DefaultInfo(
            runfiles = verilog_runner_runfiles,
            files = depset(direct = [runner_executable_file]),
            executable = runner_executable_file,
        )

    else:
        # Generator I/O
        generator_inputs = srcs + hdrs + runfiles + extra_runfiles
        generator_outputs = [tcl, script, filelist]

        # Tarball inputs
        tar_inputs = []
        for f in generator_inputs:
            tar_inputs.append(f.path)
        for f in generator_outputs:
            tar_inputs.append(f)

        # Write generator script
        verilog_runner_cmd += " >/dev/null"
        tar_cmd = [
            "tar --dereference -czf",
            ctx.outputs.tarball.path,
        ] + tar_inputs + [" >/dev/null"]
        tar_cmd = " ".join(tar_cmd)
        generator_cmd = "\n".join([verilog_runner_cmd, tar_cmd])
        generator = ctx.label.name + "_generator.sh"
        generator_executable_file = ctx.actions.declare_file(generator)
        _write_executable_shell_script(
            ctx = ctx,
            executable_file = generator_executable_file,
            cmd = generator_cmd,
            verbose = False,
            env_exports = env_exports,
        )

        # Run generator script
        ctx.actions.run(
            inputs = generator_inputs + [generator_executable_file],
            outputs = [ctx.outputs.tarball],
            executable = generator_executable_file,
            arguments = [],
            use_default_shell_env = True,
            progress_message = "Generating FPV sandbox for %{label}",
        )

        # Write runner script (but don't run it)
        untar_cmd = ["tar -xzf " + ctx.outputs.tarball.basename]
        run_cmd = ["source " + script]
        runner_cmd = "\n".join(untar_cmd + run_cmd)
        _write_executable_shell_script(
            ctx = ctx,
            executable_file = ctx.outputs.runscript,
            cmd = runner_cmd,
        )

        return DefaultInfo(
            files = depset(direct = [ctx.outputs.tarball, ctx.outputs.runscript]),
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

def _verilog_fpv_args(ctx):
    extra_args = []
    if ctx.attr.elab_only:
        extra_args.append("--elab_only")
    if ctx.attr.gui:
        extra_args.append("--gui")
    if len(ctx.attr.opts) > 0 and ctx.attr.tool == "":
        fail("If opts are provided, then tool must also be set.")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")
    for opt in ctx.attr.elab_opts:
        extra_args.append("--elab_opt='" + opt + "'")
    for opt in ctx.attr.analysis_opts:
        extra_args.append("--analysis_opt='" + opt + "'")
    return extra_args

def _verilog_fpv_test_impl(ctx):
    """Implementation of the verilog_fpv_test rule."""
    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "fpv",
        extra_args = _verilog_fpv_args(ctx),
    )

def _verilog_fpv_sandbox_impl(ctx):
    """Implementation of the rule_verilog_fpv_sandbox rule."""

    # Check if the filename ends with '.tar.gz'
    if not ctx.outputs.tarball.basename.endswith(".tar.gz"):
        fail("The 'tarball' attribute must be a file ending with '.tar.gz', but got '{}'.".format(ctx.outputs.tarball.basename))

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "fpv",
        test = False,
        extra_args = _verilog_fpv_args(ctx),
    )

# Rule definitions
rule_verilog_elab_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design elaborates. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.",
    implementation = _verilog_elab_test_impl,
    attrs = {
        "deps": attr.label_list(allow_files = False, providers = [VerilogInfo], doc = "The dependencies of the test."),
        "defines": attr.string_list(doc = "Preprocessor defines to pass to the Verilog compiler."),
        "params": attr.string_dict(doc = "Verilog module parameters to set in the instantiation of the top-level module."),
        "top": attr.string(doc = "The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name."),
        "verilog_runner_tool": attr.label(doc = "The Verilog Runner tool to use.", default = "//python/verilog_runner:verilog_runner.py", allow_files = True),
        "verilog_runner_plugins": attr.label_list(
            default = ["//python/verilog_runner/plugins:iverilog.py"],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(doc = "Elaboration tool to use. If not provided, default is decided by the Verilog Runner tool implementation with available plugins."),
        "custom_tcl_header": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script." +
                   "The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "custom_tcl_body": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step." +
                   "The tcl body (custom or not) is unconditionally followed by the tcl footer." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
    },
    test = True,
)

def verilog_elab_test(tags = [], **kwargs):
    """Wraps rule_verilog_elab_test with extra tags.

    Args:
        tags: The tags to add to the test. If not provided, then defaults to:
            * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.
            * resources:verilog_elab_test_tool_licenses:1 -- indicates that the test requires a elaboration tool license.
            * elab -- useful for test filtering, e.g., bazel test //... --test_tag_filters=elab
            * If the tool is provided in kwargs, then the tool name is added to the above tags.
        **kwargs: Other arguments to pass to the rule_verilog_elab_test rule.
    """

    extra_tags = [
        "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
        "resources:verilog_elab_test_tool_licenses:1",
        "elab",
    ]

    if "tool" in kwargs:
        extra_tags.append(kwargs["tool"])

    rule_verilog_elab_test(
        tags = tags + extra_tags,
        **kwargs
    )

rule_verilog_lint_test = rule(
    doc = "Tests that a Verilog or SystemVerilog design passes a set of static lint checks. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.",
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
        "verilog_runner_tool": attr.label(doc = "The Verilog Runner tool to use.", default = "//python/verilog_runner:verilog_runner.py", allow_files = True),
        "verilog_runner_plugins": attr.label_list(
            default = ["//python/verilog_runner/plugins:iverilog.py"],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(doc = "Lint tool to use. If not provided, default is decided by the Verilog Runner tool implementation with available plugins."),
        "custom_tcl_header": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script." +
                   "The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "custom_tcl_body": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step." +
                   "The tcl body (custom or not) is unconditionally followed by the tcl footer." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
    },
    test = True,
)

def verilog_lint_test(tags = [], **kwargs):
    """Wraps rule_verilog_lint_test with extra tags.

    Args:
        tags: The tags to add to the test. If not provided, then defaults to:
            * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.
            * resources:verilog_lint_test_tool_licenses:1 -- indicates that the test requires a lint tool license.
            * lint -- useful for test filtering, e.g., bazel test //... --test_tag_filters=lint
            * If the tool is provided in kwargs, then the tool name is added to the above tags.
        **kwargs: Other arguments to pass to the rule_verilog_lint_test rule.
    """

    extra_tags = [
        "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
        "resources:verilog_lint_test_tool_licenses:1",
        "lint",
    ]

    if "tool" in kwargs:
        extra_tags.append(kwargs["tool"])

    rule_verilog_lint_test(
        tags = tags + extra_tags,
        **kwargs
    )

rule_verilog_sim_test = rule(
    doc = """
    Runs Verilog/SystemVerilog compilation and simulation in one command. This rule should be used for simple unit tests that do not require multi-step compilation, elaboration, and simulation. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.
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
        "verilog_runner_tool": attr.label(doc = "The Verilog Runner tool to use.", default = "//python/verilog_runner:verilog_runner.py", allow_files = True),
        "verilog_runner_plugins": attr.label_list(
            default = ["//python/verilog_runner/plugins:iverilog.py"],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(
            doc = "Simulator tool to use. If not provided, default is decided by the Verilog Runner tool implementation with available plugins.",
        ),
        "custom_tcl_header": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script." +
                   "The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "custom_tcl_body": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step." +
                   "The tcl body (custom or not) is unconditionally followed by the tcl footer." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
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

def verilog_sim_test(tool = None, opts = [], tags = [], **kwargs):
    """Wraps rule_verilog_sim_test with extra tags.

    Args:
        tool: The simulation tool to use.
        opts: Tool-specific options not covered by other arguments.
        tags: The tags to add to the test. If not provided, then defaults to:
            * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.
            * resources:verilog_sim_test_tool_licenses:1 -- indicates that the test requires a simulation tool license.
            * sim -- useful for test filtering, e.g., bazel test //... --test_tag_filters=sim
            * If the tool is provided, then the tool name is added to the above tags.
        **kwargs: Other arguments to pass to the rule_verilog_sim_test rule.
    """

    extra_tags = [
        "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
        "resources:verilog_sim_test_tool_licenses:1",
        "sim",
        tool,
    ]

    # Make sure we fail the test ASAP after any error occurs (assertion or otherwise).
    extra_opts = []
    if tool == "vcs":
        extra_opts.append("-assert global_finish_maxfail=1+offending_values")
    elif tool == "dsim":
        extra_opts.append("-exit-on-error 1")

    rule_verilog_sim_test(
        tool = tool,
        opts = opts + extra_opts,
        tags = tags + extra_tags,
        **kwargs
    )

rule_verilog_fpv_test = rule(
    doc = """
    Runs Verilog/SystemVerilog compilation and formal verification in one command. This rule should be used for simple formal unit tests. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.
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
        "elab_opts": attr.string_list(
            doc = "custom elab options",
        ),
        "analysis_opts": attr.string_list(
            doc = "custom analysis options",
        ),
        "elab_only": attr.bool(
            doc = "Only run elaboration.",
            default = False,
        ),
        "verilog_runner_tool": attr.label(doc = "The Verilog Runner tool to use.", default = "//python/verilog_runner:verilog_runner.py", allow_files = True),
        "verilog_runner_plugins": attr.label_list(
            default = ["//python/verilog_runner/plugins:iverilog.py"],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(
            doc = "Formal tool to use. If not provided, default is decided by the Verilog Runner tool implementation with available plugins.",
        ),
        "custom_tcl_header": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script." +
                   "The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "custom_tcl_body": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step." +
                   "The tcl body (custom or not) is unconditionally followed by the tcl footer." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "gui": attr.bool(
            doc = "Enable GUI.",
            default = False,
        ),
    },
    test = True,
)

def verilog_fpv_test(tags = [], **kwargs):
    """Wraps rule_verilog_fpv_test with extra tags.

    Args:
        tags: The tags to add to the test. If not provided, then defaults to:
            * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.
            * resources:verilog_fpv_test_tool_licenses:1 -- indicates that the test requires a formal tool license.
            * fpv -- useful for test filtering, e.g., bazel test //... --test_tag_filters=fpv
            * If the tool is provided in kwargs, then the tool name is added to the above tags.
        **kwargs: Other arguments to pass to the rule_verilog_fpv_test rule.
    """
    extra_tags = [
        "no-sandbox",  # Preserves miscellaneous undeclared EDA tool outputs for debugging
        "resources:verilog_fpv_test_tool_licenses:1",
        "fpv",
    ]
    if "tool" in kwargs:
        extra_tags.append(kwargs["tool"])

    rule_verilog_fpv_test(
        tags = tags + extra_tags,
        **kwargs
    )

rule_verilog_fpv_sandbox = rule(
    doc = "Writes FPV files and run scripts into a tarball for independent execution outside of Bazel.",
    implementation = _verilog_fpv_sandbox_impl,
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
        "elab_opts": attr.string_list(
            doc = "custom elab options",
        ),
        "analysis_opts": attr.string_list(
            doc = "custom analysis options",
        ),
        "elab_only": attr.bool(
            doc = "Only run elaboration.",
            default = False,
        ),
        "verilog_runner_tool": attr.label(doc = "The Verilog Runner tool to use.", default = "//python/verilog_runner:verilog_runner.py", allow_files = True),
        "verilog_runner_plugins": attr.label_list(
            default = ["//python/verilog_runner/plugins:iverilog.py"],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(
            doc = "Tool to use. If not provided, default is decided by the Verilog Runner tool implementation with available plugins.",
        ),
        "custom_tcl_header": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script." +
                   "The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "custom_tcl_body": attr.label(
            doc = ("Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step." +
                   "The tcl body (custom or not) is unconditionally followed by the tcl footer." +
                   "Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation."),
            allow_single_file = [".tcl"],
        ),
        "gui": attr.bool(
            doc = "Enable GUI.",
            default = False,
        ),
    },
    outputs = {
        "tarball": "%{name}.tar.gz",
        "runscript": "%{name}_runner.sh",
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

def verilog_fpv_test_suite(name, defines = [], params = {}, illegal_param_combinations = {}, sandbox = True, **kwargs):
    """Creates a suite of Verilog fpv tests for each combination of the provided parameters.

    The function generates all possible combinations of the provided parameters and creates a verilog_fpv_test
    for each combination. The test names are generated by appending "_fpv_test"
    to the base name followed by the parameter key-values.

    Args:
        name (str): The base name for the test suite.
        defines (list): A list of defines.
        params (dict): A dictionary where keys are parameter names and values are lists of possible values for those parameters.
        illegal_param_combinations (dict): A dictionary where keys are parameter tuples and values are lists of illegal values for those parameters.
        sandbox (bool): Whether to create a sandbox for the test.
        **kwargs: Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.
    """
    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = _cartesian_product(param_values_list)

    # Create a verilog_fpv_test for each combination of parameters
    for param_combination in param_combinations:
        params = dict(zip(param_keys, param_combination))

        # Check if this combination is illegal
        skip = False
        for keys_tuple, disallowed_values in illegal_param_combinations.items():
            values_tuple = tuple([params[k] for k in keys_tuple])
            if values_tuple in disallowed_values:
                skip = True
                break
        if not skip:
            verilog_fpv_test(
                name = _make_test_name(name, "fpv_test", param_keys, param_combination),
                defines = defines,
                params = params,
                **kwargs
            )
            if sandbox:
                rule_verilog_fpv_sandbox(
                    name = _make_test_name(name, "fpv_sandbox", param_keys, param_combination),
                    defines = defines,
                    params = params,
                    **kwargs
                )

def verilog_sim_test_suite(name, defines = [], params = {}, **kwargs):
    """Creates a suite of Verilog sim tests for each combination of the provided parameters.

    The function generates all possible combinations of the provided parameters and creates a verilog_sim_test
    for each combination. The test names are generated by appending "_sim_test"
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

    # Create a verilog_sim_test for each combination of parameters
    for param_combination in param_combinations:
        params = dict(zip(param_keys, param_combination))
        verilog_sim_test(
            name = _make_test_name(name, "sim_test", param_keys, param_combination),
            defines = defines,
            params = params,
            **kwargs
        )
