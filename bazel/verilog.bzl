# SPDX-License-Identifier: Apache-2.0

"""Verilog rules for Bazel."""

load("@rules_hdl//verilog:providers.bzl", "VerilogInfo", "verilog_library")

TOOLS_THAT_NEED_LICENSES = [
    "ascentlint",
    "jg",
    "vcf",
    "vcs",
    "xrun",
]
COVERAGE_TYPES = [
    "toggle",
    "line",
    "branch",
    "expr",
    "covergroup",
    "user",
]
COVERAGE_NAME_MAPPING = {
    "user": "cover properties",
}
COVERAGE_DATA_FILENAME = "coverage.dat"

def extra_tags(kind, tool):
    """Returns a list of extra tags that should be added to a target.

    Args:
        kind: The kind of target.
        tool: The tool name.

    Returns:
        A list of extra tags. Specifically:
            * The kind of target -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<kind>
            * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
            * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
    """
    extra_tags = [
        kind,
        tool,
    ]
    if tool in TOOLS_THAT_NEED_LICENSES:
        extra_tags.append("resources:verilog_test_tool_licenses_" + tool + ":1")
    return extra_tags

def _with_manual_tag(tags):
    """Returns tags with the manual tag included."""
    if "manual" in tags:
        return tags
    return tags + ["manual"]

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

def _shell_quote(value):
    """Single-quotes a shell word, reopening quotes around each literal `'`."""
    return "'" + value.replace("'", "'\"'\"'") + "'"

def _append_env_exports(lines, env_exports):
    if env_exports:
        for key, value in env_exports.items():
            lines.append("export {}={}".format(key, value))

def _append_wrapper_prologue(lines, env_exports, verilog_runner_env):
    """Appends the hook/no-hook environment setup in its required order."""

    # Bazel 9 exports an rlocation compatibility function whose body contains a
    # literal "ERROR:" message. Some EDA plugins scan captured shell output for
    # diagnostics, so keep that helper out of child tool environments.
    unset_rlocation = "unset -f rlocation 2>/dev/null || true"

    if verilog_runner_env:
        # The hook may inspect or replace Bazel's runfiles helper before it is
        # kept out of child tool environments. Bedrock exports come last so
        # plugin directories are appended to values established by the hook.
        lines.append("source " + _shell_quote(verilog_runner_env))
        lines.append(unset_rlocation)
        _append_env_exports(lines, env_exports)
    else:
        # Preserve the pre-hook wrapper order when no hook is configured.
        _append_env_exports(lines, env_exports)
        lines.append(unset_rlocation)

def _execution_path(file, use_runfiles):
    """Returns a runfiles path for direct wrappers or execroot path for actions."""
    return file.short_path if use_runfiles else file.path

def _execution_dir(file, use_runfiles):
    """Returns the directory containing a file in the selected execution mode."""
    return "/".join(_execution_path(file, use_runfiles).split("/")[:-1])

def _write_executable_shell_script(ctx, executable_file, cmd, verbose = True, env_exports = None, verilog_runner_env = None):
    """Writes a shell script that executes the given command and returns a handle to it."""
    lines = [
        "#!/usr/bin/env bash",
        "set -ex" if verbose else "set -e",
    ]

    _append_wrapper_prologue(lines, env_exports, verilog_runner_env)

    if verbose:
        lines.append("pwd")
    lines.append(cmd)
    lines.append("")
    ctx.actions.write(
        output = executable_file,
        content = "\n".join(lines),
        is_executable = True,
    )

def _cov_type_to_provider(cov_type):
    return cov_type + "_info"

_VERILOG_COVERAGE_DATA_FIELDS = [_cov_type_to_provider(t) for t in COVERAGE_TYPES] + ["coverage_data", "coverage_failures"]

VerilogRunnerFlagsInfo = provider(
    fields = ["name", "runner_flags"],
    doc = "Verilog Runner flags provider",
)

VerilogCoverageDataInfo = provider(
    fields = _VERILOG_COVERAGE_DATA_FIELDS,
    doc = "Verilator raw coverage data and info artifacts.",
)

VerilogCoverageReportInfo = provider(
    fields = _VERILOG_COVERAGE_DATA_FIELDS + ["srcs"],
    doc = "Coverview coverage info and Verilator coverage data artifacts.",
)

def _runner_flags_impl(ctx):
    runner_flags = ctx.build_setting_value.split(" ")

    return [
        VerilogRunnerFlagsInfo(
            name = ctx.label.name,
            runner_flags = runner_flags,
        ),
    ]

runner_flags = rule(
    doc = """
      Build configuration for Verilog Runner flags from command line
    """,
    implementation = _runner_flags_impl,
    build_setting = config.string(flag = True),
)

def _verilog_runner_env_attr():
    return attr.label(
        doc = """Optional shell script sourced immediately before each Verilog Runner invocation.

The wrapper does not change directories before sourcing the hook, so it inherits
the wrapper's existing working directory. Direct wrappers add the hook to
runfiles and source its runfiles path; sandbox generator actions declare it as
an input and source its execroot path. A direct hook is sourced before the
wrapper unsets any inherited `rlocation` function, but callers needing runfiles
lookup must initialize a working runfiles library rather than assume that Bazel
exports a usable `rlocation` implementation. Bedrock appends its
`verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the
hook runs. The hook is not included in sandbox archives or sourced by their
final runners.""",
        allow_single_file = True,
        cfg = "exec",
    )

def _verilog_base_impl(ctx, subcmd, test = True, extra_args = [], extra_runfiles = [], allow_empty_top = False):
    """Shared implementation for rule_verilog_elab_test, rule_verilog_lint_test, rule_verilog_sim_test, and rule_verilog_fpv_test.

    Args:
        ctx: ctx for the rule
        subcmd (string): the tool subcommand to run
        test (bool, optional): whether the rule is a test; if not, then generate a tarball sandbox
        extra_args (list of strings, optional): tool-specific args
        extra_runfiles (list of files, optional): tool-specific files
        allow_empty_top (bool, optional): whether the rule may omit a top module

    Returns:
        DefaultInfo for the rule that describes the runfiles, depset, and executable
    """
    data_files = getattr(ctx.files, "data", [])
    runfiles = list(data_files)
    verilog_runner_files_to_run = ctx.attr.verilog_runner_tool[DefaultInfo].files_to_run
    verilog_runner_files = ctx.files.verilog_runner_tool
    verilog_runner_file = None

    # Bazel may expose a single source file or filegroup through files_to_run;
    # raw runner sources still need to be invoked through Python.
    if (
        len(verilog_runner_files) == 1 and
        verilog_runner_files[0].is_source and
        verilog_runner_files[0].basename.endswith(".py")
    ):
        verilog_runner_file = verilog_runner_files[0]
        verilog_runner_executable = None
    else:
        verilog_runner_executable = verilog_runner_files_to_run.executable
    if test or not verilog_runner_executable:
        runfiles += ctx.files.verilog_runner_tool
    runfiles += ctx.files.verilog_runner_data
    runfiles += ctx.files.verilog_runner_plugins
    verilog_runner_env = ctx.file.verilog_runner_env
    if test and verilog_runner_env:
        runfiles.append(verilog_runner_env)
    srcs = get_transitive(ctx = ctx, srcs_not_hdrs = True).to_list()
    hdrs = get_transitive(ctx = ctx, srcs_not_hdrs = False).to_list()
    use_runfiles = test
    src_files = [_execution_path(src, use_runfiles) for src in srcs]
    hdr_files = [_execution_path(hdr, use_runfiles) for hdr in hdrs]
    top = ctx.attr.top
    if top == "" and not allow_empty_top:
        if (len(ctx.attr.deps) != 1):
            fail("If the top attribute is not provided, then there must be exactly one dependency.")
        top = ctx.attr.deps[0].label.name
    args = (["--hdr=" + hdr for hdr in hdr_files] +
            ["--define=" + define for define in ctx.attr.defines] +
            ["--param=" + key + "=\"" + value + "\"" for key, value in ctx.attr.params.items()])
    if top:
        args.append("--top=" + top)
    filelist = ctx.label.name + ".f"
    tcl = ctx.label.name + ".tcl"
    script = ctx.label.name + ".sh"
    log = ctx.label.name + ".log"
    args.append("--filelist=" + filelist)
    args.append("--tcl=" + tcl)
    args.append("--script=" + script)
    args.append("--log=" + log)
    args.append("--tool='" + ctx.attr.tool + "'")
    if not test:
        args.append("--dry-run")
    if ctx.attr.custom_tcl_header:
        args.append("--custom_tcl_header=" + _execution_path(ctx.files.custom_tcl_header[0], use_runfiles))
        runfiles += ctx.files.custom_tcl_header
    if ctx.attr.custom_tcl_body:
        args.append("--custom_tcl_body=" + _execution_path(ctx.files.custom_tcl_body[0], use_runfiles))
        runfiles += ctx.files.custom_tcl_body
    if ctx.attr.runner_flags:
        args += ctx.attr.runner_flags[VerilogRunnerFlagsInfo].runner_flags
    args += extra_args

    generator_tools = []
    if not verilog_runner_executable:
        if len(verilog_runner_files) != 1:
            fail("verilog_runner_tool must be an executable target or a single Python source file.")
        verilog_runner_file = verilog_runner_files[0]

    if verilog_runner_executable:
        runner_cmd_prefix = [_execution_path(verilog_runner_executable, use_runfiles)]
    else:
        runner_cmd_prefix = ["python3", _execution_path(verilog_runner_file, use_runfiles)]
    if not test and verilog_runner_executable:
        generator_tools = [verilog_runner_files_to_run]
    plugin_paths = []
    for plugin in ctx.files.verilog_runner_plugins:
        plugin_dir = _execution_dir(plugin, use_runfiles)
        if plugin_dir not in plugin_paths:
            plugin_paths.append(plugin_dir)
    verilog_runner_plugin_paths = ":".join(plugin_paths)
    env_exports = {
        "VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP": "${VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP}",
        "VERILOG_RUNNER_PLUGIN_PATH": "${VERILOG_RUNNER_PLUGIN_PATH}:" + verilog_runner_plugin_paths,
    }

    verilog_runner_cmd = " ".join(runner_cmd_prefix + [subcmd] + args + src_files)
    verilog_runner_env_path = None
    if verilog_runner_env:
        verilog_runner_env_path = _execution_path(verilog_runner_env, use_runfiles)
    verilog_runner_runfiles = ctx.runfiles(files = srcs + hdrs + runfiles + extra_runfiles)
    if test:
        verilog_runner_runfiles = verilog_runner_runfiles.merge(
            ctx.attr.verilog_runner_tool[DefaultInfo].default_runfiles,
        )
    if test:
        runner = ctx.label.name + "_runner.sh"
        runner_executable_file = ctx.actions.declare_file(runner)
        _write_executable_shell_script(
            ctx = ctx,
            executable_file = runner_executable_file,
            cmd = verilog_runner_cmd,
            env_exports = env_exports,
            verilog_runner_env = verilog_runner_env_path,
        )
        return DefaultInfo(
            runfiles = verilog_runner_runfiles,
            files = depset(direct = [runner_executable_file]),
            executable = runner_executable_file,
        )

    else:
        # Generator I/O
        generator_inputs = srcs + hdrs + runfiles + extra_runfiles
        if verilog_runner_env:
            generator_inputs.append(verilog_runner_env)
        generator_outputs = [tcl, script, filelist]

        # Tarball inputs
        tar_inputs = []
        for f in srcs + hdrs + runfiles + extra_runfiles:
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
            verilog_runner_env = verilog_runner_env_path,
        )

        # Run generator script
        ctx.actions.run(
            inputs = generator_inputs + [generator_executable_file],
            outputs = [ctx.outputs.tarball],
            executable = generator_executable_file,
            arguments = [],
            tools = generator_tools,
            use_default_shell_env = True,
            progress_message = "Generating " + subcmd.upper() + " sandbox for %{label}",
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
    extra_args = []
    if ctx.attr.compile_only:
        extra_args.append("--compile_only")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")
    return _verilog_base_impl(
        allow_empty_top = ctx.attr.compile_only,
        ctx = ctx,
        subcmd = "elab",
        extra_args = extra_args,
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
    if ctx.attr.opts and ctx.attr.tool != "vcs":
        fail("'opts' is a deprecated VCS-only simulation option. Use 'elab_opts' or 'sim_opts' instead.")
    if ctx.attr.elab_only:
        extra_args.append("--elab_only")
    if ctx.attr.uvm:
        extra_args.append("--uvm")
    extra_args.append("--seed='" + str(ctx.attr.seed) + "'")
    if ctx.attr.waves:
        extra_args.append("--waves")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")
    for opt in ctx.attr.elab_opts:
        extra_args.append("--elab_opt='" + opt + "'")
    for opt in ctx.attr.sim_opts:
        extra_args.append("--sim_opt='" + opt + "'")

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "sim",
        extra_args = extra_args,
    )

def _verilog_synth_args(ctx):
    """Returns generic command-line arguments for a synthesis invocation."""
    extra_args = []
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")
    return extra_args

def _verilog_yosys_synth_args(ctx):
    """Returns Yosys-specific command-line arguments for synthesis."""
    extra_args = _verilog_synth_args(ctx)
    if bool(ctx.attr.input_driver_cell) != bool(ctx.attr.output_load_ff):
        fail("input_driver_cell and output_load_ff must be specified together")
    if ctx.attr.liberties:
        if not ctx.attr.liberty_root:
            fail("liberty_root is required with liberties")
        if sorted(ctx.attr.liberty_sha256.keys()) != sorted(ctx.attr.liberties):
            fail("liberty_sha256 must specify exactly one digest for each entry in liberties")
        if ctx.attr.sequential_liberty and ctx.attr.sequential_liberty not in ctx.attr.liberties:
            fail("sequential_liberty must also be present in liberties")
    elif (
        ctx.attr.sequential_liberty or
        ctx.attr.liberty_root or
        ctx.attr.liberty_sha256 or
        ctx.attr.input_driver_cell or
        ctx.attr.output_load_ff
    ):
        fail("Sequential mapping, Liberty metadata, and I/O constraints require liberties")

    for liberty in ctx.attr.liberties:
        extra_args.append("--liberty='" + liberty + "'")
    if ctx.attr.sequential_liberty:
        extra_args.append("--sequential_liberty='" + ctx.attr.sequential_liberty + "'")
    if ctx.attr.liberty_root:
        extra_args.append('--liberty_root="' + ctx.attr.liberty_root + '"')
    for liberty, digest in sorted(ctx.attr.liberty_sha256.items()):
        extra_args.append("--liberty_sha256='" + liberty + "=" + digest + "'")
    if ctx.attr.liberties:
        extra_args.append("--synth_profile='" + ctx.attr.synth_profile + "'")
    elif ctx.attr.clock_period_ps:
        fail("clock_period_ps requires liberties")
    if ctx.attr.clock_period_ps:
        extra_args.append("--clock_period_ps=" + str(ctx.attr.clock_period_ps))
    if ctx.attr.input_driver_cell:
        extra_args.append("--input_driver_cell='" + ctx.attr.input_driver_cell + "'")
        extra_args.append("--output_load_ff='" + ctx.attr.output_load_ff + "'")
    return extra_args

def _verilog_synth_impl(ctx):
    """Implementation of the verilog_synth executable rule."""
    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "synth",
        extra_args = _verilog_synth_args(ctx),
    )

def _verilog_synth_sandbox_impl(ctx):
    """Implementation of the rule_verilog_synth_sandbox rule."""
    if not ctx.outputs.tarball.basename.endswith(".tar.gz"):
        fail("The 'tarball' attribute must be a file ending with '.tar.gz', but got '{}'.".format(ctx.outputs.tarball.basename))

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "synth",
        test = False,
        extra_args = _verilog_synth_args(ctx),
    )

def _coverage_name(coverage_type):
    return COVERAGE_NAME_MAPPING.get(coverage_type, coverage_type)

def _coverage_report_info(coverage_infos_by_type, coverage_data, coverage_failures, srcs):
    return VerilogCoverageReportInfo(
        toggle_info = coverage_infos_by_type.get("toggle", []),
        line_info = coverage_infos_by_type.get("line", []),
        branch_info = coverage_infos_by_type.get("branch", []),
        expr_info = coverage_infos_by_type.get("expr", []),
        covergroup_info = coverage_infos_by_type.get("covergroup", []),
        user_info = coverage_infos_by_type.get("user", []),
        coverage_data = coverage_data,
        coverage_failures = coverage_failures,
        srcs = srcs,
    )

def _coverage_data_info(coverage_infos_by_type, coverage_data, coverage_failures):
    return VerilogCoverageDataInfo(
        toggle_info = coverage_infos_by_type.get("toggle", []),
        line_info = coverage_infos_by_type.get("line", []),
        branch_info = coverage_infos_by_type.get("branch", []),
        expr_info = coverage_infos_by_type.get("expr", []),
        covergroup_info = coverage_infos_by_type.get("covergroup", []),
        user_info = coverage_infos_by_type.get("user", []),
        coverage_data = coverage_data,
        coverage_failures = coverage_failures,
    )

def _append_coverage_infos(coverage_infos_by_type, coverage_provider):
    for coverage_type in COVERAGE_TYPES:
        coverage_infos = getattr(coverage_provider, _cov_type_to_provider(coverage_type), [])
        if len(coverage_infos) == 0:
            continue
        coverage_infos_by_type[coverage_type] += coverage_infos

def _source_verilog_runner_eda_tools_env_setup():
    return [
        'if [[ -n "$VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP" ]]; then',
        '  source "$VERILOG_RUNNER_EDA_TOOLS_ENV_SETUP"',
        "fi",
    ]

def _declare_coverage_info_files(ctx, coverage_data, info_process, name, coverage_dat_path = None):
    if coverage_dat_path == None:
        coverage_dat_path = coverage_data.path

    coverage_infos = []
    description_files = []
    dataset_data = {}
    for coverage_type in COVERAGE_TYPES:
        raw_coverage_info = ctx.actions.declare_file("raw_coverage_{}_{}.info".format(coverage_type, name))
        coverage_info = ctx.actions.declare_file("coverage_{}_{}.info".format(coverage_type, name))

        command_prefix = ["set -e"] + _source_verilog_runner_eda_tools_env_setup()
        ctx.actions.run_shell(
            inputs = [coverage_data],
            outputs = [raw_coverage_info],
            command = "\n".join(command_prefix + [
                "if test -s {coverage_dat_path}; then",
                "  " + " ".join([
                    "\"${{VERILATOR_COVERAGE_CMD:-verilator_coverage}}\"",
                    "--filter-type {coverage_type}",
                    "--write-info {coverage_info_path} {coverage_dat_path}",
                ]),
                "else",
                "  : > {coverage_info_path}",
                "fi",
            ]).format(
                coverage_dat_path = _shell_quote(coverage_dat_path),
                coverage_type = _shell_quote(coverage_type),
                coverage_info_path = _shell_quote(raw_coverage_info.path),
            ),
            mnemonic = "VerilatorCoverageInfo",
            progress_message = "Creating Verilator coverage info for %{label}",
            use_default_shell_env = True,
        )

        ctx.actions.run_shell(
            inputs = [raw_coverage_info],
            outputs = [coverage_info],
            command = " ".join([
                # Filter out all sim sources and path outside of the repository
                "{info_process} transform --filter-out '^(/|[^/]+/sim/)'",
                "--output {coverage_info} {raw_coverage_info}",
            ]).format(
                info_process = _shell_quote(info_process.executable.path),
                coverage_info = _shell_quote(coverage_info.path),
                raw_coverage_info = _shell_quote(raw_coverage_info.path),
            ),
            tools = [info_process],
            mnemonic = "CoverviewInfoTransform",
            progress_message = "Filtering coverage info for %{label}",
            use_default_shell_env = True,
        )

        coverage_infos.append(coverage_info)
        dataset_data[_coverage_name(coverage_type)] = [coverage_info.basename]

    return coverage_infos, description_files, dataset_data

def _write_coverview_base_config(ctx, name, dataset_data, output):
    config = {
        "repo": "bedrock-rtl",
        "hide_not_covered": True,
        "datasets": {
            name: dataset_data,
        },
    }
    ctx.actions.write(
        output = output,
        content = json.encode(config),
    )

def _pack_coverview_archive(ctx, info_process, output, config, coverage_infos, description_files = [], srcs = [], hdrs = []):
    command_args = (
        [_shell_quote(info_process.executable.path), "pack", "--output", _shell_quote(output.path), "--coverage-files"] +
        [_shell_quote(info.path) for info in coverage_infos]
    )
    if description_files:
        command_args += ["--description-files"] + [_shell_quote(desc.path) for desc in description_files]
    command_args += ["--config", _shell_quote(config.path)]

    ctx.actions.run_shell(
        inputs = coverage_infos + description_files + srcs + hdrs + [config],
        outputs = [output],
        command = " ".join(command_args),
        tools = [info_process],
        mnemonic = "CoverviewPack",
        progress_message = "Packing coverage into ZIP for %{label}",
        use_default_shell_env = True,
    )

def _verilog_sim_coverage_data_impl(ctx):
    """Implementation of the Verilator coverage info and description rule."""
    extra_args = []
    if ctx.attr.opts and ctx.attr.tool != "vcs":
        fail("'opts' is a deprecated VCS-only simulation option. Use 'elab_opts' or 'sim_opts' instead.")
    if ctx.attr.tool != "verilator":
        fail("'coverage' is only supported with tool = 'verilator'.")
    if ctx.attr.elab_only:
        fail("'coverage' cannot be combined with 'elab_only'.")
    if ctx.attr.uvm:
        extra_args.append("--uvm")
    extra_args.append("--seed='" + str(ctx.attr.seed) + "'")
    if ctx.attr.waves:
        extra_args.append("--waves")
    raw_coverage_data = ctx.actions.declare_directory(ctx.attr.name + "_coverage")
    coverage_log = ctx.actions.declare_file(ctx.attr.name + ".log")
    coverage_failure = ctx.actions.declare_file(ctx.attr.name + "_coverage_failures.txt")
    coverage_dat_path = raw_coverage_data.path + "/" + COVERAGE_DATA_FILENAME
    coverage_dat = _shell_quote(coverage_dat_path)
    extra_args.extend(["--coverage", coverage_dat])
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")
    for opt in ctx.attr.elab_opts:
        extra_args.append("--elab_opt='" + opt + "'")
    for opt in ctx.attr.sim_opts:
        extra_args.append("--sim_opt='" + opt + "'")
    verilog_test = _verilog_base_impl(ctx = ctx, subcmd = "sim", extra_args = extra_args)

    runner_cmd = " ".join([verilog_test.files.to_list()[0].path])
    command = "\n".join([
        "set -e",
        "rm -rf {raw_coverage_data}",
        "mkdir -p {raw_coverage_data}",
        ": > {coverage_failure}",
        "set +e",
        "{runner_cmd} > {coverage_log} 2>&1",
        "status=$?",
        "set -e",
        "if [[ $status -ne 0 ]] ; then",
        "  rm -f {coverage_dat}",
        "  cat {coverage_log} >&2",
        "  printf '%s\\n' '{label} failed with exit status '\"${{status}}\" > {coverage_failure}",
        "  echo '  log: {coverage_log}' >> {coverage_failure}",
        "fi",
    ]).format(
        label = str(ctx.label),
        runner_cmd = runner_cmd,
        raw_coverage_data = _shell_quote(raw_coverage_data.path),
        coverage_failure = _shell_quote(coverage_failure.path),
        coverage_log = _shell_quote(coverage_log.path),
        coverage_dat = coverage_dat,
    )

    ctx.actions.run_shell(
        inputs = verilog_test.files.to_list() + ctx.files.verilog_runner_plugins,
        tools = [verilog_test.default_runfiles.files],
        outputs = [raw_coverage_data, coverage_log, coverage_failure],
        command = command,
        mnemonic = "VerilatorCoverageData",
        progress_message = "Generating Verilator coverage data for %{label}",
        use_default_shell_env = True,
    )

    info_process = ctx.attr._info_process_bin[DefaultInfo].files_to_run
    coverage_infos, description_files, _ = _declare_coverage_info_files(
        ctx = ctx,
        coverage_data = raw_coverage_data,
        coverage_dat_path = coverage_dat_path,
        info_process = info_process,
        name = ctx.attr.name,
    )
    coverage_infos_by_type = {}
    for index, coverage_type in enumerate(COVERAGE_TYPES):
        coverage_infos_by_type[coverage_type] = [coverage_infos[index]]

    return [
        DefaultInfo(files = depset(coverage_infos + description_files + [raw_coverage_data, coverage_log, coverage_failure])),
        _coverage_data_info(
            coverage_infos_by_type = coverage_infos_by_type,
            coverage_data = [raw_coverage_data],
            coverage_failures = [coverage_failure],
        ),
    ]

def _verilog_sim_coverage_aggregate_impl(ctx):
    """Implementation of the Coverview coverage aggregation rule."""
    srcs = get_transitive(ctx = ctx, srcs_not_hdrs = True).to_list()
    hdrs = get_transitive(ctx = ctx, srcs_not_hdrs = False).to_list()
    coverage_targets = ctx.attr.coverage_data + ctx.attr.coverage_reports
    s = []
    for coverage_report in ctx.attr.coverage_reports:
        s += coverage_report[VerilogCoverageReportInfo].srcs
    srcs += depset(s).to_list()

    if len(coverage_targets) == 0:
        fail("At least one entry must be provided in 'coverage_data' or 'coverage_reports'.")

    info_process = ctx.attr._info_process_bin[DefaultInfo].files_to_run
    coverage_infos_by_type = {}
    for coverage_type in COVERAGE_TYPES:
        coverage_infos_by_type[coverage_type] = []
    coverage_data_inputs = []
    coverage_dat_paths = []
    coverage_failures = []

    for coverage_target in ctx.attr.coverage_data:
        coverage_info = coverage_target[VerilogCoverageDataInfo]
        coverage_data_inputs += coverage_info.coverage_data
        coverage_dat_paths += [coverage_data.path + "/" + COVERAGE_DATA_FILENAME for coverage_data in coverage_info.coverage_data]
        coverage_failures += coverage_info.coverage_failures
        _append_coverage_infos(coverage_infos_by_type, coverage_info)

    for coverage_target in ctx.attr.coverage_reports:
        coverage_report = coverage_target[VerilogCoverageReportInfo]
        coverage_data_inputs += coverage_report.coverage_data
        coverage_dat_paths += [coverage_data.path for coverage_data in coverage_report.coverage_data]
        coverage_failures += coverage_report.coverage_failures
        _append_coverage_infos(coverage_infos_by_type, coverage_report)

    merged_coverage_data = ctx.actions.declare_file(ctx.attr.name + ".dat")
    merged_coverage_failures = ctx.actions.declare_file(ctx.attr.name + "_coverage_failures.txt")
    coverage_dat_paths = [_shell_quote(coverage_dat_path) for coverage_dat_path in coverage_dat_paths]
    coverage_failure_paths = [_shell_quote(coverage_failure.path) for coverage_failure in coverage_failures]
    command_prefix = ["set -e"] + _source_verilog_runner_eda_tools_env_setup()
    ctx.actions.run_shell(
        inputs = coverage_data_inputs + coverage_failures,
        outputs = [merged_coverage_data, merged_coverage_failures],
        command = "\n".join(command_prefix + [
            # Gather failed coverages
            ": > {merged_coverage_failures}",
            "for failure in {coverage_failure_paths}; do",
            "  if test -s \"${{failure}}\"; then",
            "    cat \"${{failure}}\" >> {merged_coverage_failures}",
            "    echo >> {merged_coverage_failures}",
            "  fi",
            "done",
            "if test -s {merged_coverage_failures}; then",
            # Exit when one of coverage data was not collected
            "  exit 1",
            "fi",
            # Create list of coverage .dat files
            "coverage_data=()",
            "for coverage_dat in {coverage_dat_paths}; do",
            "  if test -s \"${{coverage_dat}}\"; then",
            "    coverage_data+=(\"${{coverage_dat}}\")",
            "  fi",
            "done",
            # Merge coverage data
            "if (( ${{#coverage_data[@]}} )); then",
            "  \"${{VERILATOR_COVERAGE_CMD:-verilator_coverage}}\" -write {merged_coverage_data} \"${{coverage_data[@]}}\"",
            "else",
            "  echo 'No Verilator coverage data files were produced.' >&2",
            "  : > {merged_coverage_data}",
            "fi",
        ]).format(
            coverage_failure_paths = " ".join(coverage_failure_paths),
            merged_coverage_failures = _shell_quote(merged_coverage_failures.path),
            coverage_dat_paths = " ".join(coverage_dat_paths),
            merged_coverage_data = _shell_quote(merged_coverage_data.path),
        ),
        mnemonic = "VerilatorCoverageDataMerge",
        progress_message = "Merging Verilator coverage data for %{label}",
        use_default_shell_env = True,
    )

    # Ensures that all files are available in the final report
    if ctx.files.all_srcs:
        all_srcs_info = ctx.actions.declare_file("coverage_all_srcs_{}.info".format(ctx.attr.name))
        ctx.actions.write(
            output = all_srcs_info,
            content = "TN:all_sources\n" + "\n".join(
                ["SF:" + file.path + "\nend_of_record" for file in ctx.files.all_srcs],
            ),
        )
        coverage_infos_by_type[COVERAGE_TYPES[-1]].append(all_srcs_info)

    merged_coverage_infos = []
    merged_description_files = []
    dataset_data = {}
    for coverage_type in COVERAGE_TYPES:
        merged_coverage_info = ctx.actions.declare_file("coverage_{}_{}.info".format(coverage_type, ctx.attr.name))
        merged_description_file = ctx.actions.declare_file("tests_{}_{}.desc".format(coverage_type, ctx.attr.name))
        coverage_infos_for_type = coverage_infos_by_type[coverage_type]
        coverage_info_files = [_shell_quote(coverage_info.path) for coverage_info in coverage_infos_for_type]
        ctx.actions.run_shell(
            inputs = coverage_infos_for_type,
            outputs = [merged_coverage_info, merged_description_file],
            command = " ".join([
                "{info_process} merge",
                "--test-list {merged_description_file}",
                "--test-list-strip coverage_{coverage_type}_,_coverage_data.info",
                "--output {merged_coverage_info}",
                "{coverage_info_files}",
            ]).format(
                info_process = _shell_quote(info_process.executable.path),
                merged_description_file = _shell_quote(merged_description_file.path),
                merged_coverage_info = _shell_quote(merged_coverage_info.path),
                coverage_type = coverage_type,
                coverage_info_files = " ".join(coverage_info_files),
            ),
            tools = [info_process],
            mnemonic = "CoverviewInfoMerge",
            progress_message = "Merging coverage info for %{label}",
            use_default_shell_env = True,
        )
        merged_coverage_infos.append(merged_coverage_info)
        merged_description_files.append(merged_description_file)
        dataset_data[_coverage_name(coverage_type)] = [merged_coverage_info.basename, merged_description_file.basename]

    config = ctx.actions.declare_file("config_{}.json".format(ctx.attr.name))
    _write_coverview_base_config(
        ctx = ctx,
        name = ctx.attr.name,
        dataset_data = dataset_data,
        output = config,
    )

    _pack_coverview_archive(
        ctx = ctx,
        info_process = info_process,
        output = ctx.outputs.coverage_zip,
        config = config,
        coverage_infos = merged_coverage_infos,
        description_files = merged_description_files,
        srcs = srcs + ctx.files.all_srcs,
        hdrs = hdrs,
    )

    run_config_path = ctx.outputs.coverage_zip.path.replace(".zip", "_run_config.json")
    run_zip_path = ctx.outputs.coverage_zip.path.replace(".zip", "_run.zip")
    run_pack_args = (
        [_shell_quote(info_process.executable.path), "pack", "--output", _shell_quote(run_zip_path), "--coverage-files"] +
        [_shell_quote(info.path) for info in merged_coverage_infos]
    )
    if merged_description_files:
        run_pack_args += ["--description-files"] + [_shell_quote(desc.path) for desc in merged_description_files]
    run_pack_args += ["--config", _shell_quote(run_config_path)]

    runscript = ctx.actions.declare_file(ctx.attr.name + "_runner.sh")
    ctx.actions.write(
        output = runscript,
        content = "\n".join(
            [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
                "workspace_dir=\"${BUILD_WORKSPACE_DIRECTORY:-}\"",
                "if [[ -z \"${workspace_dir}\" ]]; then",
                "  workspace_dir=\"${PWD}\"",
                "fi",
                "cd \"${workspace_dir}\"",
                "mkdir -p " + _shell_quote(ctx.outputs.coverage_zip.dirname),
                "workspace_dir=\"${BUILD_WORKSPACE_DIRECTORY:-}\"",
                "if [ -z \"${workspace_dir}\" ]; then",
                "  workspace_dir=\"$(git -C \"${BUILD_WORKING_DIRECTORY:-${PWD}}\" rev-parse --show-toplevel 2>/dev/null || pwd)\"",
                "fi",
                "branch=\"$(git -C \"${workspace_dir}\" branch --show-current 2>/dev/null || true)\"",
                "if [ -z \"${branch}\" ]; then",
                "  branch=\"$(git -C \"${workspace_dir}\" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)\"",
                "fi",
                "jq \\",
                "  --arg branch \"${branch}\" \\",
                "  --arg commit \"$(git -C \"${workspace_dir}\" rev-parse HEAD 2>/dev/null || echo unknown)\" \\",
                "  --arg timestamp \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\" \\",
                "  --arg verilator \"$(\"${VERILATOR_CMD:-verilator}\" --version 2>/dev/null || echo unknown)\" \\",
                "  '",
                "  .additional = (if (.additional | type) == \"object\" then .additional else {} end)",
                "  | .additional.verilator = $verilator",
                "  | .branch = $branch",
                "  | .commit = $commit",
                "  | .timestamp = $timestamp",
                "' " + _shell_quote(config.path) + " > " + _shell_quote(run_config_path),
                " ".join(run_pack_args),
                "echo " + _shell_quote("Deterministic coverage archive: " + ctx.outputs.coverage_zip.path),
                "echo " + _shell_quote("Run config: " + run_config_path),
                "echo " + _shell_quote("Run-stamped coverage archive: " + run_zip_path),
                "",
            ],
        ),
        is_executable = True,
    )

    return [
        DefaultInfo(
            files = depset([
                ctx.outputs.coverage_zip,
                merged_coverage_data,
                merged_coverage_failures,
            ]),
            runfiles = ctx.runfiles(
                files = [ctx.outputs.coverage_zip, config, info_process.executable] + merged_coverage_infos + merged_description_files + srcs + ctx.files.all_srcs + hdrs,
            ).merge(ctx.attr._info_process_bin[DefaultInfo].default_runfiles),
            executable = runscript,
        ),
        _coverage_report_info(
            coverage_infos_by_type = coverage_infos_by_type,
            coverage_data = [merged_coverage_data],
            coverage_failures = [merged_coverage_failures],
            srcs = srcs,
        ),
    ]

def _verilog_yosys_synth_impl(ctx):
    """Implementation of the Yosys synthesis executable rule."""
    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "synth",
        extra_args = _verilog_yosys_synth_args(ctx),
    )

def _verilog_yosys_synth_sandbox_impl(ctx):
    """Implementation of the Yosys synthesis sandbox rule."""
    if not ctx.outputs.tarball.basename.endswith(".tar.gz"):
        fail("The 'tarball' attribute must be a file ending in '.tar.gz', but got '{}'".format(ctx.outputs.tarball.basename))

    return _verilog_base_impl(
        ctx = ctx,
        subcmd = "synth",
        test = False,
        extra_args = _verilog_yosys_synth_args(ctx),
    )

def _verilog_fpv_args(ctx):
    extra_args = []
    if ctx.attr.elab_only:
        extra_args.append("--elab_only")
    if ctx.attr.gui:
        extra_args.append("--gui")
    for opt in ctx.attr.opts:
        extra_args.append("--opt='" + opt + "'")
    for opt in ctx.attr.elab_opts:
        extra_args.append("--elab_opt='" + opt + "'")
    for opt in ctx.attr.analysis_opts:
        extra_args.append("--analysis_opt='" + opt + "'")
    if ctx.attr.conn:
        extra_args.append("--conn")
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
        "compile_only": attr.bool(doc = "Compile and type-check sources without elaborating a top-level module."),
        "opts": attr.string_list(doc = "Tool-specific elaboration options."),
        "top": attr.string(doc = "The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name."),
        "verilog_runner_tool": attr.label(doc = "The Verilog Runner tool to use.", default = "//python/verilog_runner:verilog_runner.py", allow_files = True),
        "verilog_runner_env": _verilog_runner_env_attr(),
        "verilog_runner_data": attr.label_list(
            default = ["//python/verilog_runner:verilog_runner_data"],
            allow_files = True,
            doc = "Additional Verilog Runner files needed at runtime.",
        ),
        "verilog_runner_plugins": attr.label_list(
            default = [
                "//python/verilog_runner/plugins:slang.py",
                "//python/verilog_runner/plugins:verilator.py",
            ],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(doc = "Elaboration tool to use.", mandatory = True),
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
        "runner_flags": attr.label(
            doc = "command line flags",
            allow_files = False,
            providers = [VerilogRunnerFlagsInfo],
            default = "//bazel:runner_flags",
        ),
    },
    test = True,
)

def verilog_elab_test(
        name,
        tool,
        tags = [],
        **kwargs):
    """Wraps rule_verilog_elab_test and appends extra tags.

    The following extra tags are unconditionally appended to the list of tags:
        * elab -- useful for test filtering, e.g., bazel test //... --test_tag_filters=elab
        * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
        * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
        * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.

    Args:
        name: test name
        tool: The elaboration tool to use.
        tags: The tags to add to the test.
        **kwargs: Other arguments to pass to the rule_verilog_elab_test rule.
    """

    rule_verilog_elab_test(
        name = name,
        tool = tool,
        tags = tags + extra_tags("elab", tool) + ["no-sandbox"],
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
        "verilog_runner_env": _verilog_runner_env_attr(),
        "verilog_runner_data": attr.label_list(
            default = ["//python/verilog_runner:verilog_runner_data"],
            allow_files = True,
            doc = "Additional Verilog Runner files needed at runtime.",
        ),
        "verilog_runner_plugins": attr.label_list(
            default = [
                "//python/verilog_runner/plugins:verilator.py",
            ],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(doc = "Lint tool to use.", mandatory = True),
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
        "runner_flags": attr.label(
            doc = "command line flags",
            allow_files = False,
            providers = [VerilogRunnerFlagsInfo],
            default = "//bazel:runner_flags",
        ),
    },
    test = True,
)

def verilog_lint_test(tool, tags = [], **kwargs):
    """Wraps rule_verilog_lint_test with a default tool and appends extra tags.

    The following extra tags are unconditionally appended to the list of tags:
        * lint -- useful for test filtering, e.g., bazel test //... --test_tag_filters=lint
        * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
        * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
        * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.

    Args:
        tool: The lint tool to use.
        tags: The tags to add to the test.
        **kwargs: Other arguments to pass to the rule_verilog_lint_test rule.
    """

    rule_verilog_lint_test(
        tool = tool,
        tags = tags + extra_tags("lint", tool) + ["no-sandbox"],
        **kwargs
    )

def _verilog_synth_attrs(
        verilog_runner_tool_default = "//python/verilog_runner:verilog_runner.py",
        verilog_runner_plugins_default = [],
        tool_default = None):
    """Returns the common attributes for runnable and sandbox synthesis rules."""
    attrs = {
        "deps": attr.label_list(
            doc = "Verilog libraries containing the design to synthesize.",
            allow_files = False,
            providers = [VerilogInfo],
        ),
        "defines": attr.string_list(
            doc = "Preprocessor defines to pass to the synthesis frontend.",
        ),
        "params": attr.string_dict(
            doc = "Top-level Verilog module parameter overrides.",
        ),
        "top": attr.string(
            doc = "Top-level module; defaults to the sole dependency's label name.",
        ),
        "opts": attr.string_list(
            doc = "Tool-specific synthesis frontend options.",
        ),
        "data": attr.label_list(
            doc = "Additional runtime files needed by the synthesis plugin.",
            allow_files = True,
        ),
        "verilog_runner_tool": attr.label(
            doc = "The Verilog Runner tool to use.",
            default = verilog_runner_tool_default,
            allow_files = True,
        ),
        "verilog_runner_env": _verilog_runner_env_attr(),
        "verilog_runner_data": attr.label_list(
            default = ["//python/verilog_runner:verilog_runner_data"],
            allow_files = True,
            doc = "Additional Verilog Runner files needed at runtime.",
        ),
        "verilog_runner_plugins": attr.label_list(
            default = verilog_runner_plugins_default,
            allow_files = True,
            doc = "Verilog Runner synthesis plugins to load from this workspace.",
        ),
        "custom_tcl_header": attr.label(
            doc = "Optional tool-specific Tcl header.",
            allow_single_file = [".tcl"],
        ),
        "custom_tcl_body": attr.label(
            doc = "Optional tool-specific Tcl body.",
            allow_single_file = [".tcl"],
        ),
        "runner_flags": attr.label(
            doc = "Command-line flags forwarded to Verilog Runner.",
            allow_files = False,
            providers = [VerilogRunnerFlagsInfo],
            default = "//bazel:runner_flags",
        ),
    }
    if tool_default == None:
        attrs["tool"] = attr.string(
            doc = "Synthesis tool plugin to use.",
            mandatory = True,
        )
    else:
        attrs["tool"] = attr.string(
            doc = "Synthesis tool plugin to use.",
            default = tool_default,
        )
    return attrs

def _verilog_yosys_synth_attrs(verilog_runner_tool_default = "//python/verilog_runner:verilog_runner.py"):
    """Returns attributes for the runnable and sandbox Yosys rules."""
    attrs = _verilog_synth_attrs(
        verilog_runner_plugins_default = ["//python/verilog_runner/plugins:yosys.py"],
        verilog_runner_tool_default = verilog_runner_tool_default,
        tool_default = "yosys",
    )
    attrs.update({
        "liberties": attr.string_list(
            doc = "System Liberty paths relative to liberty_root.",
        ),
        "sequential_liberty": attr.string(
            doc = "Liberty path used for sequential-cell mapping when libraries are split; must also appear in liberties.",
        ),
        "liberty_root": attr.string(
            doc = "Runtime root path for system-provided Liberty files. Shell environment references are expanded by the generated Bazel wrapper.",
        ),
        "liberty_sha256": attr.string_dict(
            doc = "Expected SHA-256 digest for every entry in liberties.",
        ),
        "synth_profile": attr.string(
            doc = "Stable synthesis profile recorded in generated reports.",
            default = "generic",
        ),
        "clock_period_ps": attr.int(
            doc = "Optional target clock period in picoseconds; requires liberties.",
        ),
        "input_driver_cell": attr.string(
            doc = "Optional Liberty cell assumed to drive each primary input; requires output_load_ff.",
        ),
        "output_load_ff": attr.string(
            doc = "Optional capacitive load in femtofarads on each primary output; requires input_driver_cell.",
        ),
    })
    return attrs

rule_verilog_synth = rule(
    doc = "Runs logic synthesis for a Verilog or SystemVerilog design and prints the tool report. This is an executable target, not a test.",
    implementation = _verilog_synth_impl,
    attrs = _verilog_synth_attrs(),
    executable = True,
)

rule_verilog_synth_sandbox = rule(
    doc = "Writes logic-synthesis inputs and generated scripts into a tarball for independent execution outside Bazel.",
    implementation = _verilog_synth_sandbox_impl,
    attrs = _verilog_synth_attrs("//python/verilog_runner:verilog_runner"),
    outputs = {
        "tarball": "%{name}.tar.gz",
        "runscript": "%{name}_runner.sh",
    },
)

rule_verilog_yosys_synth = rule(
    doc = "Runs Yosys logic synthesis and prints its raw report.",
    implementation = _verilog_yosys_synth_impl,
    attrs = _verilog_yosys_synth_attrs(),
    executable = True,
)

rule_verilog_yosys_synth_sandbox = rule(
    doc = "Writes Yosys synthesis inputs and generated scripts into a reproduction tarball.",
    implementation = _verilog_yosys_synth_sandbox_impl,
    attrs = _verilog_yosys_synth_attrs("//python/verilog_runner:verilog_runner"),
    outputs = {
        "tarball": "%{name}.tar.gz",
        "runscript": "%{name}_runner.sh",
    },
)

def verilog_synth(name, tool, tags = [], **kwargs):
    """Creates a runnable logic-synthesis target that streams the raw tool report.

    The tool string selects a Verilog Runner synthesis plugin, so callers can
    use the bundled Yosys plugin or provide another open-source or proprietary
    synthesis plugin through `verilog_runner_plugins`. Tool-specific attributes
    belong in a tool adapter such as `verilog_yosys_synth`.

    Example:
        ```starlark
        verilog_synth(
            name = "fifo_synth",
            tool = "yosys",
            deps = [":fifo"],
            top = "fifo",
            params = {"Depth": "16", "Width": "32"},
        )
        ```

    Args:
        name: Target name.
        tool: Synthesis plugin name.
        tags: Additional Bazel tags.
        **kwargs: Arguments forwarded to rule_verilog_synth.
    """
    rule_verilog_synth(
        name = name,
        tool = tool,
        tags = tags + extra_tags("synth", tool),
        **kwargs
    )

def verilog_synth_sandbox(name, tool, tags = [], **kwargs):
    """Creates a portable logic-synthesis reproduction archive.

    The archive contains the transitive Verilog source and header closure,
    Verilog Runner plugin files, and generated filelist, Tcl, and shell scripts.
    The synthesis tool executable remains a system dependency.

    Args:
        name: Target name.
        tool: Synthesis plugin name.
        tags: Additional Bazel tags.
        **kwargs: Arguments forwarded to rule_verilog_synth_sandbox.
    """
    rule_verilog_synth_sandbox(
        name = name,
        tool = tool,
        tags = tags + extra_tags("synth-sandbox", tool),
        **kwargs
    )

def verilog_yosys_synth(name, tool = "yosys", tags = [], **kwargs):
    """Creates a runnable Yosys synthesis target.

    Args:
        name: Target name.
        tool: Must be `yosys`; accepted so this function can be used by the generic sweep macro.
        tags: Additional Bazel tags.
        **kwargs: Arguments forwarded to rule_verilog_yosys_synth.
    """
    if tool != "yosys":
        fail("verilog_yosys_synth only supports tool = 'yosys'")
    rule_verilog_yosys_synth(
        name = name,
        tags = tags + extra_tags("synth", "yosys"),
        **kwargs
    )

def verilog_yosys_synth_sandbox(name, tool = "yosys", tags = [], **kwargs):
    """Creates a Yosys synthesis reproduction archive.

    Args:
        name: Target name.
        tool: Must be `yosys`; accepted so this function can be used by the generic sweep macro.
        tags: Additional Bazel tags.
        **kwargs: Arguments forwarded to rule_verilog_yosys_synth_sandbox.
    """
    if tool != "yosys":
        fail("verilog_yosys_synth_sandbox only supports tool = 'yosys'")
    rule_verilog_yosys_synth_sandbox(
        name = name,
        tags = tags + extra_tags("synth-sandbox", "yosys"),
        **kwargs
    )

def _verilog_sim_attrs(verilog_runner_tool_default = "//python/verilog_runner:verilog_runner.py", use_info_process = False):
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
            doc = "Deprecated VCS-only simulation options. Prefer 'elab_opts' or 'sim_opts'.",
        ),
        "elab_opts": attr.string_list(
            doc = "Tool-specific compile/elaboration options not covered by other arguments.",
        ),
        "sim_opts": attr.string_list(
            doc = "Tool-specific simulation runtime options, such as simulator plusargs.",
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
        "verilog_runner_env": _verilog_runner_env_attr(),
        "verilog_runner_data": attr.label_list(
            default = ["//python/verilog_runner:verilog_runner_data"],
            allow_files = True,
            doc = "Additional Verilog Runner files needed at runtime.",
        ),
        "verilog_runner_plugins": attr.label_list(
            default = [
                "//python/verilog_runner/plugins:verilator.py",
            ],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "tool": attr.string(
            doc = "Simulator tool to use.",
            mandatory = True,
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
        "runner_flags": attr.label(
            doc = "command line flags",
            allow_files = False,
            providers = [VerilogRunnerFlagsInfo],
            default = "//bazel:runner_flags",
        ),
    }
    if use_info_process:
        attrs.update({
            "_info_process_bin": attr.label(
                doc = "info-process Python package",
                default = "//python/verilog_runner:info_process",
                cfg = "exec",
                executable = True,
            ),
        })
    return attrs

rule_verilog_sim_test = rule(
    doc = """
    Runs Verilog/SystemVerilog compilation and simulation in one command. This rule should be used for simple unit tests that do not require multi-step compilation, elaboration, and simulation. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.
    """,
    implementation = _verilog_sim_test_impl,
    attrs = _verilog_sim_attrs(),
    test = True,
)

rule_verilog_sim_coverage_data = rule(
    doc = """
    Runs a Verilator simulation test target and emits coverage info and description files.
    """,
    implementation = _verilog_sim_coverage_data_impl,
    attrs = _verilog_sim_attrs(use_info_process = True),
    provides = [VerilogCoverageDataInfo],
)

rule_verilog_sim_coverage_aggregate = rule(
    doc = """
    Merges coverage info files and packs a Coverview ZIP as a declared Bazel output.
    """,
    implementation = _verilog_sim_coverage_aggregate_impl,
    attrs = {
        "coverage_data": attr.label_list(
            doc = "Coverage data targets whose info files should be merged.",
            default = [],
            providers = [VerilogCoverageDataInfo],
        ),
        "coverage_reports": attr.label_list(
            doc = "Coverage report targets whose transitive info files should be merged.",
            default = [],
            providers = [VerilogCoverageReportInfo],
        ),
        "deps": attr.label_list(
            doc = "The dependencies of the testbench whose design sources should be included in sources.txt.",
            allow_files = False,
            providers = [VerilogInfo],
            default = [],
        ),
        "all_srcs": attr.label(
            doc = "Target defining all sources that should be included in the aggregated coverage.",
            allow_files = False,
            default = None,
        ),
        "_info_process_bin": attr.label(
            doc = "info-process Python package",
            default = "//python/verilog_runner:info_process",
            cfg = "exec",
            executable = True,
        ),
    },
    outputs = {
        "coverage_zip": "%{name}.zip",
    },
    executable = True,
)

def verilog_sim_coverage_data(tool, opts = [], elab_opts = [], sim_opts = [], tags = [], waves = False, **kwargs):
    """Wraps rule_verilog_sim_coverage_data.

    Args:
        name: The name of the coverage info and description target.
        tool: The simulation tool to use. Must be "verilator".
        opts: Deprecated VCS-only simulation options.
        elab_opts: Tool-specific compile/elaboration options not covered by other arguments.
        sim_opts: Tool-specific simulation runtime options, such as simulator plusargs.
        waves: Enable waveform dumping.
        **kwargs: Other arguments to pass to the rule_verilog_sim_coverage_data rule.
    """
    if opts and tool != "vcs":
        fail("'opts' is a deprecated VCS-only simulation option. Use 'elab_opts' or 'sim_opts' instead.")
    if tool != "verilator":
        fail("'coverage' is only supported with tool = 'verilator'.")
    if kwargs.get("elab_only", False):
        fail("'coverage' cannot be combined with 'elab_only'.")

    # Make sure we fail the test ASAP after any error occurs (assertion or otherwise).
    extra_elab_opts = []
    extra_sim_opts = []
    tags = _with_manual_tag(tags + extra_tags("sim", tool))
    if tool == "vcs":
        # Make sure we fail the test if any assertions fail.
        extra_elab_opts = ["-assert global_finish_maxfail=1+offending_values -error=TFIPC -error=PCWM-W -error=PCWM-L"]
    elif tool == "dsim":
        extra_sim_opts.append("-exit-on-error 1")

    rule_verilog_sim_coverage_data(
        tool = tool,
        opts = opts,
        elab_opts = elab_opts + extra_elab_opts,
        sim_opts = sim_opts + extra_sim_opts,
        tags = tags,
        waves = waves,
        **kwargs
    )

def verilog_sim_coverage_aggregate(name, coverage_data = [], coverage_reports = [], deps = [], all_srcs = None, **kwargs):
    """Wraps rule_verilog_sim_coverage_aggregate.

    Args:
        name: The name of the aggregate coverage target.
        coverage_data: Coverage data targets whose info files should be merged.
        coverage_reports: Coverage report targets whose transitive info files should be merged.
        deps: The dependencies of the testbench whose design sources should be included in sources.txt.
        all_srcs: List of all source files that should be included in the coverage report.
        **kwargs: Other arguments to pass to the rule_verilog_sim_coverage_aggregate rule.
    """

    tags = _with_manual_tag(kwargs.pop("tags", []))

    rule_verilog_sim_coverage_aggregate(
        name = name,
        coverage_data = coverage_data,
        coverage_reports = coverage_reports,
        deps = deps,
        tags = tags,
        all_srcs = all_srcs,
        **kwargs
    )

def verilog_sim_test(tool, opts = [], elab_opts = [], sim_opts = [], tags = [], waves = False, **kwargs):
    """Wraps rule_verilog_sim_test with a default tool and appends extra tags.

    The following extra tags are unconditionally appended to the list of tags:
        * sim -- useful for test filtering, e.g., bazel test //... --test_tag_filters=sim
        * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
        * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
        * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.

    Args:
        tool: The simulation tool to use.
        opts: Deprecated VCS-only simulation options.
        elab_opts: Tool-specific compile/elaboration options not covered by other arguments.
        sim_opts: Tool-specific simulation runtime options, such as simulator plusargs.
        tags: The tags to add to the test.
        waves: Enable waveform dumping.
        **kwargs: Other arguments to pass to the rule_verilog_sim_test rule.
    """

    if opts and tool != "vcs":
        fail("'opts' is a deprecated VCS-only simulation option. Use 'elab_opts' or 'sim_opts' instead.")

    # Make sure we fail the test ASAP after any error occurs (assertion or otherwise).
    extra_elab_opts = []
    extra_sim_opts = []
    test_tags = tags + extra_tags("sim", tool)
    if waves:
        test_tags.append("no-sandbox")
    if tool == "vcs":
        # Make sure we fail the test if any assertions fail.
        extra_elab_opts = ["-assert global_finish_maxfail=1+offending_values -error=TFIPC -error=PCWM-W -error=PCWM-L"]
    elif tool == "dsim":
        extra_sim_opts.append("-exit-on-error 1")

    rule_verilog_sim_test(
        tool = tool,
        opts = opts,
        elab_opts = elab_opts + extra_elab_opts,
        sim_opts = sim_opts + extra_sim_opts,
        tags = test_tags,
        waves = waves,
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
        "verilog_runner_env": _verilog_runner_env_attr(),
        "verilog_runner_data": attr.label_list(
            default = ["//python/verilog_runner:verilog_runner_data"],
            allow_files = True,
            doc = "Additional Verilog Runner files needed at runtime.",
        ),
        "verilog_runner_plugins": attr.label_list(
            default = [
                "//python/verilog_runner/plugins:verilator.py",
            ],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "data": attr.label_list(
            doc = "Additional files to copy into the runfiles tree for the FPV job.",
            allow_files = True,
        ),
        "tool": attr.string(
            doc = "Formal tool to use.",
            mandatory = True,
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
        "conn": attr.bool(
            doc = "Switch to connectivity",
            default = False,
        ),
        "runner_flags": attr.label(
            doc = "jg flags",
            allow_files = False,
            providers = [VerilogRunnerFlagsInfo],
            default = "//bazel:runner_flags",
        ),
    },
    test = True,
)

def verilog_fpv_test(tool, tags = [], **kwargs):
    """Wraps rule_verilog_fpv_test with a default tool and appends extra tags.

    The following extra tags are unconditionally appended to the list of tags:
        * fpv -- useful for test filtering, e.g., bazel test //... --test_tag_filters=fpv
        * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
        * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
        * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.

    Args:
        tool: The formal verification tool to use.
        tags: The tags to add to the test.
        **kwargs: Other arguments to pass to the rule_verilog_fpv_test rule.
    """
    rule_verilog_fpv_test(
        tool = tool,
        tags = tags + extra_tags("fpv", tool) + ["no-sandbox"],
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
            doc = "Tool-specific options not covered by other arguments.",
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
        "verilog_runner_env": _verilog_runner_env_attr(),
        "verilog_runner_data": attr.label_list(
            default = ["//python/verilog_runner:verilog_runner_data"],
            allow_files = True,
            doc = "Additional Verilog Runner files needed at runtime.",
        ),
        "verilog_runner_plugins": attr.label_list(
            default = [
                "//python/verilog_runner/plugins:verilator.py",
            ],
            allow_files = True,
            doc = "Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.",
        ),
        "data": attr.label_list(
            doc = "Additional files to copy into the sandbox tarball.",
            allow_files = True,
        ),
        "tool": attr.string(
            doc = "Formal tool to use.",
            mandatory = True,
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
        "conn": attr.bool(
            doc = "Switch to connectivity",
            default = False,
        ),
        "runner_flags": attr.label(
            doc = "jg flags",
            allow_files = False,
            providers = [VerilogRunnerFlagsInfo],
            default = "//bazel:runner_flags",
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

def _abbreviate_uppercase(input_str):
    """Converts a string to one that contains only the lowercase versions of the original uppercase letters.

    For example, "EnableAssertPushStability" becomes "eaps".
    """
    return "".join([c.lower() for c in input_str.elems() if c.isupper()])

def _make_test_name(base_name, suffix, param_keys, combination):
    """Generate a unique test name based on a combination of parameter values."""
    parts = [base_name]
    for key, value in zip(param_keys, combination):
        parts.append("%s%s" % (_abbreviate_uppercase(key), value))
    parts.append(suffix)
    return "_".join(parts)

def _synth_name_token(value):
    """Normalizes a synthesis tool or library name for use in a target name."""
    token = "".join([
        c.lower() if c.lower() in "abcdefghijklmnopqrstuvwxyz0123456789" else "_"
        for c in value.elems()
    ])
    if not token.strip("_"):
        fail("synthesis tool and library names must contain an alphanumeric character")
    return token

def verilog_elab_and_lint_test_suite(
        name,
        top = None,
        deps = [],
        defines = [],
        params = {},
        elab_tools = ["verific", "slang"],
        lint_tool = "ascentlint",
        disable_lint_rules = [],
        **kwargs):
    """Creates a suite of Verilog elaboration and lint tests for each combination of the provided parameters.

    The function generates a wrapper covering all possible combinations of the provided parameters, creates a
    verilog_elab_test for each elaboration tool, and creates one verilog_lint_test. Elaboration test names append
    the tool name followed by "_elab_test"; the lint test name appends "_lint_test".

    Args:
        top (str): The top-level module to instantiate. Can be left undefined if there is only one dependency.
        deps (list): The dependencies of the test suite.
        name (str): The base name for the test suite.
        defines (list): A list of defines.
        params (dict): A dictionary where keys are parameter names and values are lists of possible values for those parameters.
        elab_tools (list of strings): The tools to use for elaboration. Defaults to Verific and Slang.
        lint_tool (str): The tool to use for linting.
        disable_lint_rules (list): A list of lint rules to disable in the generated files.
        **kwargs: Additional common keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.
    """
    if not top:
        if len(deps) != 1:
            fail("top must be provided if there is more than one dependency")
        top = deps[0][1:]

    if len(elab_tools) == 0:
        fail("elab_tools must contain at least one elaboration tool")
    seen_elab_tools = {}
    for elab_tool in elab_tools:
        if elab_tool in seen_elab_tools:
            fail("elab_tools contains a duplicate tool: " + elab_tool)
        seen_elab_tools[elab_tool] = True

    generate_parameter_file(
        name = name + "_params",
        params = params,
    )

    generate_instantiation_wrapper(
        name = name + "_wrapper_src",
        deps = deps,
        top = top,
        wrapper_name = name + "_wrapper",
        param_file = ":" + name + "_params",
        disable_lint_rules = disable_lint_rules,
    )

    verilog_library(
        name = name + "_wrapper",
        srcs = [":" + name + "_wrapper_src"],
        deps = deps,
    )

    for elab_tool in elab_tools:
        test_name = name + "_" + elab_tool + "_elab_test"
        verilog_elab_test(
            name = test_name,
            tool = elab_tool,
            deps = [":" + name + "_wrapper"],
            defines = defines,
            **kwargs
        )

    verilog_lint_test(
        name = name + "_lint_test",
        tool = lint_tool,
        deps = [":" + name + "_wrapper"],
        defines = defines,
        **kwargs
    )

def is_param_combination_legal(params, illegal_param_combinations):
    """Checks if a given combination of parameters is legal based on the provided illegal combinations.

    Args:
        params (dict): A dictionary where keys are parameter names and values are the specific value for those parameters in the current combination.
        illegal_param_combinations (dict): A dictionary where keys are tuples of parameter names and values are lists of tuples of illegal values for those parameters.

    Returns:
        True if the combination is legal, False if it is illegal.
    """
    for keys_tuple, disallowed_values in illegal_param_combinations.items():
        values_tuple = tuple([params[k] for k in keys_tuple])
        if values_tuple in disallowed_values:
            return False
    return True

def verilog_fpv_test_suite(
        name,
        defines = [],
        params = {},
        illegal_param_combinations = {},
        sandbox = True,
        verilog_fpv_test_func = None,
        verilog_fpv_sandbox_func = None,
        **kwargs):
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
        verilog_fpv_test_func (function): A function to use instead of verilog_fpv_test.
        verilog_fpv_sandbox_func (function): A function to use instead of rule_verilog_fpv_sandbox.
        **kwargs: Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.
    """

    # Set defaults if none provided
    if verilog_fpv_test_func == None:
        verilog_fpv_test_func = verilog_fpv_test
    if verilog_fpv_sandbox_func == None:
        verilog_fpv_sandbox_func = rule_verilog_fpv_sandbox

    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = _cartesian_product(param_values_list)

    # Create a verilog_fpv_test for each combination of parameters
    for param_combination in param_combinations:
        params = dict(zip(param_keys, param_combination))

        # Check if this combination is illegal
        if is_param_combination_legal(params, illegal_param_combinations):
            verilog_fpv_test_func(
                name = _make_test_name(name, "fpv_test", param_keys, param_combination),
                defines = defines,
                params = params,
                **kwargs
            )
            if sandbox:
                verilog_fpv_sandbox_func(
                    name = _make_test_name(name, "fpv_sandbox", param_keys, param_combination),
                    defines = defines,
                    params = params,
                    **kwargs
                )

def verilog_sim_test_suite(
        name,
        defines = [],
        params = {},
        illegal_param_combinations = {},
        coverage = False,
        **kwargs):
    """Creates a suite of Verilog sim tests for each combination of the provided parameters.

    The function generates all possible combinations of the provided parameters and creates a verilog_sim_test
    for each combination. The test names are generated by appending "_sim_test"
    to the base name followed by the parameter key-values.

    Args:
        name (str): The base name for the test suite.
        defines (list): A list of defines.
        params (dict): A dictionary where keys are parameter names and values are lists of possible values for those parameters.
        illegal_param_combinations (dict): A dictionary where keys are parameter tuples and values are lists of tuples of illegal values for those parameters.
        coverage (bool): Value enabling and disabling coverage data.
        **kwargs: Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.
    """
    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = _cartesian_product(param_values_list)
    tool = kwargs.get("tool", False)
    coverage_data = []

    if coverage and tool != "verilator":
        fail("'coverage' is only supported with tool = 'verilator'.")

    # Create a verilog_sim_test for each legal combination of parameters
    for param_combination in param_combinations:
        params = dict(zip(param_keys, param_combination))
        if not is_param_combination_legal(params, illegal_param_combinations):
            continue
        test_name = _make_test_name(name, "sim_test", param_keys, param_combination)
        verilog_sim_test(
            name = test_name,
            defines = defines,
            params = params,
            **kwargs
        )
        if coverage and tool == "verilator":
            coverage_data_name = _make_test_name(name, "coverage_data", param_keys, param_combination)
            verilog_sim_coverage_data(
                name = coverage_data_name,
                defines = defines,
                params = params,
                **kwargs
            )
            coverage_data.append(":" + coverage_data_name)

    if coverage:
        if "deps" not in kwargs:
            fail("'deps' must be provided when 'coverage' is enabled.")
        verilog_sim_coverage_aggregate(
            name = name + "_coverage",
            coverage_data = coverage_data,
            deps = kwargs["deps"],
        )

def verilog_synth_suite(
        name,
        defines = [],
        params = {},
        illegal_param_combinations = {},
        library_name = None,
        sandbox = True,
        sandbox_tags = None,
        tags = [],
        verilog_synth_func = None,
        verilog_synth_sandbox_func = None,
        **kwargs):
    """Creates runnable and reproducible synthesis targets for parameter combinations.

    Each runnable target delegates to `verilog_synth` and uses a deterministic
    name derived from its parameter values, tool, and mapping library. When
    `sandbox` is true, a sibling target ending in `_sandbox` packages the same
    inputs and generated scripts for execution outside Bazel.

    Args:
        name (str): Base name for generated targets.
        defines (list): Preprocessor defines for synthesis.
        params (dict): Parameter names mapped to lists of values.
        illegal_param_combinations (dict): Parameter tuples mapped to disallowed value tuples.
        library_name (str or None): Target-name identifier for the technology library/profile. Defaults to `nolib`.
        sandbox (bool): Whether to create a reproduction archive beside each runnable target.
        sandbox_tags (list or None): Tags for sandbox targets. Defaults to `tags`.
        tags (list): Tags for runnable targets.
        verilog_synth_func (function or None): Runnable-target constructor override.
        verilog_synth_sandbox_func (function or None): Sandbox-target constructor override.
        **kwargs: Additional arguments passed to verilog_synth.
    """
    if verilog_synth_func == None:
        verilog_synth_func = verilog_synth
    if verilog_synth_sandbox_func == None:
        verilog_synth_sandbox_func = verilog_synth_sandbox
    if sandbox_tags == None:
        sandbox_tags = tags

    tool = kwargs.get("tool")
    if not tool:
        fail("verilog_synth_suite requires tool")
    if library_name == None:
        library_name = "nolib"
    synth_suffix = "synth_%s_%s" % (
        _synth_name_token(tool),
        _synth_name_token(library_name),
    )

    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = _cartesian_product(param_values_list)

    for param_combination in param_combinations:
        combination_params = dict(zip(param_keys, param_combination))
        if is_param_combination_legal(combination_params, illegal_param_combinations):
            target_name = _make_test_name(name, synth_suffix, param_keys, param_combination)
            verilog_synth_func(
                name = target_name,
                defines = defines,
                params = combination_params,
                tags = tags,
                **kwargs
            )
            if sandbox:
                verilog_synth_sandbox_func(
                    name = target_name + "_sandbox",
                    defines = defines,
                    params = combination_params,
                    tags = sandbox_tags,
                    **kwargs
                )

def verilog_yosys_synth_suite(**kwargs):
    """Creates runnable and reproducible Yosys targets for a parameter sweep.

    Args:
        **kwargs: Arguments forwarded to verilog_synth_suite.
    """
    if kwargs.get("liberties") and not kwargs.get("library_name"):
        fail("verilog_yosys_synth_suite requires library_name when liberties are supplied")
    verilog_synth_suite(
        tool = "yosys",
        verilog_synth_func = verilog_yosys_synth,
        verilog_synth_sandbox_func = verilog_yosys_synth_sandbox,
        **kwargs
    )

def _generate_parameter_file_impl(ctx):
    """Implementation for the generate_parameter_file rule."""

    params = ctx.attr.params
    param_keys = sorted(params.keys())
    param_values_list = [params[key] for key in param_keys]
    param_combinations = [
        dict(zip(param_keys, [x for x in param_values]))
        for param_values in _cartesian_product(param_values_list)
    ]

    contents = json.encode({"param_sets": param_combinations})
    output_file = ctx.outputs.param_file
    ctx.actions.write(
        output = output_file,
        content = contents,
    )

    return [DefaultInfo(files = depset([output_file]))]

STITCH_TOOL_PATH = "//stitch:stitch_tool"

generate_parameter_file = rule(
    implementation = _generate_parameter_file_impl,
    attrs = {
        "params": attr.string_list_dict(mandatory = True),
    },
    outputs = {"param_file": "%{name}.json"},
)

def _generate_instantiation_wrapper_impl(ctx):
    """Implementation for the generate_instantiation_wrapper rule."""

    output_file_name = "%s.sv" % ctx.attr.name
    output_file = ctx.actions.declare_file(output_file_name)

    srcs = get_transitive(ctx = ctx, srcs_not_hdrs = True).to_list()
    hdrs = get_transitive(ctx = ctx, srcs_not_hdrs = False).to_list()
    param_files = ctx.attr.param_file.files.to_list()

    common_args = []
    disable_args = []

    for src in srcs:
        common_args.append("--sv-files")
        common_args.append(src.path)

    for hdr in hdrs:
        common_args.append("--sv-headers")
        common_args.append(hdr.path)

    for rule in ctx.attr.disable_lint_rules:
        disable_args.append("--disable-lint-rules")
        disable_args.append(rule)

    stitch_tool = ctx.attr.stitch_tool[DefaultInfo].files_to_run
    stitch_tool_inputs = ctx.files.stitch_tool
    ctx.actions.run(
        mnemonic = "GenStitchInstantiationWrapper",
        executable = stitch_tool,
        inputs = srcs + hdrs + param_files + stitch_tool_inputs,
        outputs = [output_file],
        tools = [stitch_tool],
        arguments = common_args + [
            "instantiate",
            "--module-name",
            ctx.attr.top,
            "--param-file",
            param_files[0].path,
            "--output-file",
            output_file.path,
            "--wrapper-name",
            ctx.attr.wrapper_name,
        ] + disable_args,
        use_default_shell_env = True,
    )

    return [DefaultInfo(files = depset([output_file]))]

generate_instantiation_wrapper = rule(
    implementation = _generate_instantiation_wrapper_impl,
    attrs = {
        "deps": attr.label_list(mandatory = True),
        "top": attr.string(mandatory = True),
        "param_file": attr.label(mandatory = True),
        "stitch_tool": attr.label(
            executable = True,
            cfg = "exec",
            default = Label(STITCH_TOOL_PATH),
        ),
        "wrapper_name": attr.string(mandatory = True),
        "disable_lint_rules": attr.string_list(default = []),
    },
    outputs = {"wrapper_file": "%{name}.sv"},
)
