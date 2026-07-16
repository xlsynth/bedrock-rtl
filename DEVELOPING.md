# Developing Bedrock-RTL

This guide covers the tools and checks used to develop Bedrock-RTL. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the pull-request and review policy.

## Dependencies

Install Bazel 9.1.0 (Bazelisk is recommended) and a system Python interpreter version 3.12 or newer.

The public toolchain uses Slang for elaboration, Verible for lint, Verilator for simulation, and TopStitch for RTL wrapper generation. The Docker image includes those tools, plus Yosys, EQY, Yices, and XLS support libraries.

Some checks also use tools that are not distributed with Bedrock-RTL: Verific tclmain, RealIntent AscentLint, Synopsys VCS, Cadence JasperGold, and Synopsys VCF. Provide the installations and licenses yourself if you need those checks.

## Build and test

Bedrock-RTL uses [Bazel](https://bazel.build/) to assemble source lists and run elaboration, lint, simulation, and formal tests.

```shell
bazel test //...
```

The repository includes plugins for Verilator simulation and Slang elaboration. Most other EDA-tool plugins are deliberately kept outside this repository. As a result, tests that select proprietary tools need corresponding plugins in your local or CI environment.

Keeping these plugins separate lets the test definitions remain vendor-agnostic and avoids publishing vendor API or licensing details. Not every test works with every tool; check the relevant `BUILD.bazel` target.

The Bazel test rules invoke `//python/verilog_runner/verilog_runner.py`, which provides the common tool interface used by these plugins.

To add a tool, subclass `//python/verilog_runner/eda_tool.py`, set `VERILOG_RUNNER_PLUGIN_PATH` to its module search directory, and select the tool in the relevant Bazel targets. `user.bazelrc` is a convenient place to set the environment variable.

For a Slang elaboration target, select the tool explicitly:

```bazel
verilog_elab_test(
    name = "example_elab_test",
    tool = "slang",
    top = "example",
    deps = [":example"],
)
```

Slang parses, type-checks, and elaborates the hierarchy. It supports source and header dependencies, defines, and top-level parameter overrides. For package-only source sets, set `compile_only = True`.

To refresh the public RTL PPA report, run:

```shell
bazel run //python/ppa:generate_ppa
```

## Pre-commit hooks

Install the hooks before contributing:

```shell
pre-commit install
```

This installs the pre-commit and pre-push hooks from `.pre-commit-config.yaml`. Run `pre-commit run` to invoke them manually. The repository has been tested with pre-commit 4.0.1.

## Docker development image

The `Dockerfile` builds an x86-64 Rocky Linux 8 image with the minimum dependencies and public tools. It does not include proprietary EDA tools or their licenses.

### Use a published image

Prebuilt `linux/amd64` images are published to the [Bedrock-RTL development package on GitHub Container Registry](https://github.com/orgs/xlsynth/packages/container/package/bedrock-rtl-dev). Each immutable tag has the form `YYYY-MM-DD-<full-git-sha>`; there is no moving `latest` tag.

Copy the newest date-prefixed tag from the package page, then run:

```shell
docker pull ghcr.io/xlsynth/bedrock-rtl-dev:<tag>
docker run --rm -it -v "$(pwd)":/src -w /src ghcr.io/xlsynth/bedrock-rtl-dev:<tag> /bin/bash
```

The package is public, so no registry authentication is required. Immutable tags make local and CI toolchains reproducible.

### Build an image locally

```shell
docker build --platform=linux/amd64 --tag=bedrock-rtl-dev:${USER} .
docker run --rm -it -v "$(pwd)":/src -w /src bedrock-rtl-dev:${USER} /bin/bash
```

Inside the container, try:

```shell
bazel build //... && bazel test //fifo/sim/... --test_tag_filters=verilator
```

## Continuous integration and image publishing

GitHub Actions builds the public Docker image and runs Python/ecc code generation, Stardoc, Slang, and Verilator checks in parallel. The `bazel-oss-tool-test` check verifies shard coverage and reports their combined result. A self-hosted job runs `bazel build //...` plus Verific, AscentLint, and VCS tests. Sampled JasperGold formal tests run nightly. See `.github/workflows/ci.yml` and `.github/workflows/nightly.yml` for details.

Public CI shards restore a shared Docker layer cache; only a trusted `main` or manually dispatched run updates it. Bazel disk caches are partitioned by test shard, so repeated runs restore the relevant outputs while pull requests restore caches without saving them.

After public-tool checks succeed on `main` or a manually dispatched run, CI publishes the tested image to `ghcr.io/xlsynth/bedrock-rtl-dev` with its immutable tag and a signed GitHub artifact attestation. Pull requests build the image but do not publish it. Repository maintainers can publish manually from the [CI workflow](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml) by selecting **Run workflow** and a Git ref.

## Style guide

Bedrock-RTL follows the [xlsynth Verilog Style Guide](https://github.com/xlsynth/verilog-style-guides/blob/master/VerilogCodingStyle.md), a fork of the [lowRISC style guide](https://github.com/lowrisc/verilog-style-guides/blob/master/VerilogCodingStyle.md) with minor differences.
