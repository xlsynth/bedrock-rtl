# SPDX-License-Identifier: Apache-2.0

"""Analysis tests for the optional Verilog Runner environment hook."""

load("@bazel_skylib//lib:unittest.bzl", "analysistest", "asserts")

_ENV_BASENAME = "runner_env.sh"

def _has_basename(files, basename):
    return any([file.basename == basename for file in files])

def _direct_runfiles_test_impl(ctx):
    env = analysistest.begin(ctx)
    target = analysistest.target_under_test(env)
    runfiles = target[DefaultInfo].default_runfiles.files.to_list()
    asserts.true(env, _has_basename(runfiles, _ENV_BASENAME))
    return analysistest.end(env)

direct_runfiles_test = analysistest.make(_direct_runfiles_test_impl)

def _omitted_runfiles_test_impl(ctx):
    env = analysistest.begin(ctx)
    target = analysistest.target_under_test(env)
    runfiles = target[DefaultInfo].default_runfiles.files.to_list()
    asserts.false(env, _has_basename(runfiles, _ENV_BASENAME))
    return analysistest.end(env)

omitted_runfiles_test = analysistest.make(_omitted_runfiles_test_impl)

def _fpv_generator_inputs_test_impl(ctx):
    env = analysistest.begin(ctx)
    actions = analysistest.target_actions(env)
    tar_actions = [
        action
        for action in actions
        if any([output.basename.endswith(".tar.gz") for output in action.outputs.to_list()])
    ]
    asserts.equals(env, 1, len(tar_actions))
    if tar_actions:
        asserts.true(env, _has_basename(tar_actions[0].inputs.to_list(), _ENV_BASENAME))
    return analysistest.end(env)

fpv_generator_inputs_test = analysistest.make(_fpv_generator_inputs_test_impl)

def verilog_env_analysis_test_suite(name, direct_target, fpv_sandbox_target, omitted_target):
    """Instantiates analysis tests for Verilog Runner environment wiring."""
    direct_runfiles_test(
        name = name + "_direct_runfiles",
        target_under_test = direct_target,
    )
    omitted_runfiles_test(
        name = name + "_omitted_runfiles",
        target_under_test = omitted_target,
    )
    fpv_generator_inputs_test(
        name = name + "_fpv_generator_inputs",
        target_under_test = fpv_sandbox_target,
    )
    native.test_suite(
        name = name,
        tests = [
            name + "_direct_runfiles",
            name + "_fpv_generator_inputs",
            name + "_omitted_runfiles",
        ],
    )
