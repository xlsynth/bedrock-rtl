<!-- SPDX-License-Identifier: Apache-2.0 -->

# Bedrock-RTL

![GitHub License](https://img.shields.io/github/license/xlsynth/bedrock-rtl?color=blue)
![language - SystemVerilog](https://img.shields.io/badge/language-SystemVerilog-blue)
![build system - Bazel](https://img.shields.io/badge/build%20system-Bazel-blue)
![rtl-files](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/rtl.json)

[![pre-commit](https://img.shields.io/github/check-runs/xlsynth/bedrock-rtl/main?nameFilter=pre-commit&label=pre-commit)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Apre-commit)
[![oss-tools](https://img.shields.io/github/check-runs/xlsynth/bedrock-rtl/main?nameFilter=bazel-oss-tool-test&label=oss%20tools)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-oss-tool-test)
[![build-and-proprietary-tools](https://img.shields.io/github/check-runs/xlsynth/bedrock-rtl/main?nameFilter=bazel-build-and-proprietary-tool-test&label=build-and-proprietary-tools)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-build-and-proprietary-tool-test)
[![bazel-test-python](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/python.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-oss-tool-test)
[![bazel-test-stardoc](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/stardoc.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-oss-tool-test)
[![bazel-test-verific](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/verific.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-build-and-proprietary-tool-test)
[![bazel-test-slang](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/slang.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-oss-tool-test)
[![bazel-test-ascentlint](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/ascentlint.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-build-and-proprietary-tool-test)
[![bazel-test-vcs](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/vcs.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-build-and-proprietary-tool-test)
[![bazel-test-verilator](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/verilator.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/ci.yml?query=job%3Abazel-oss-tool-test)
<!-- [![bazel-test-jg](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/mgottscho/c66dc2ddc0e513ba06ce338620977b26/raw/jg.json)](https://github.com/xlsynth/bedrock-rtl/actions/workflows/nightly.yml?query=job%3Abazel-test-jg) -->
[![open bugs](https://img.shields.io/github/issues/xlsynth/bedrock-rtl/bug?label=bugs)](https://github.com/xlsynth/bedrock-rtl/issues?q=is%3Aissue%20state%3Aopen%20label%3Abug)

High quality and composable RTL libraries in SystemVerilog

<img src="bedrock-rtl-logo-light.jpg" alt="Bedrock-RTL" width="300">

## Overview

Bedrock-RTL is a collection of reusable, composable SystemVerilog building blocks. It is for designers who want to assemble common hardware functions from well-tested libraries instead of starting each one from scratch.

- Synthesizable RTL libraries for common functions, including AMBA components, arbiters, clock-domain crossings, FIFOs, flow control, memory helpers, and counters.
- SystemVerilog macros for registers, assertions, gate wrappers, assignments, and other small building blocks.
- Assertions and formal-verification support that check both module behavior and how modules are connected.
- Bazel rules and test helpers for elaboration, lint, simulation, and formal verification.

## Design approach

The design style favors correct-by-construction interfaces: make valid use clear, catch invalid parameters at elaboration time, and check integration assumptions in the design itself. The libraries aim to make correct designs easier to build and integration mistakes easier to find.

Assertions are a normal part of integration, not an optional afterthought. Define `BR_ASSERT_ON` when you integrate Bedrock modules so that public and integration checks are active. Bedrock leaves its internal implementation checks off by default for user designs. See [Assertions](MACROS.md#assertions) for the available controls.

## Integrate Bedrock-RTL

You can use Bedrock-RTL with Bazel or use its SystemVerilog sources directly. In both cases, pin the revision you depend on.

### Use Bazel

Add Bedrock-RTL to your project's `MODULE.bazel`. This example uses the [Bazel module system](https://docs.bazel.build/versions/5.1.0/bzlmod.html) and pins a Git commit:

<details>
<summary><code>MODULE.bazel</code></summary>

```starlark
module(name = "your-project")

bazel_dep(name = "bedrock-rtl", version = "0.0.1")
git_override(
    module_name = "bedrock-rtl",
    commit = <fill_in_git_commit_sha>,
    remote = "https://github.com/xlsynth/bedrock-rtl",
)

rules_hdl_extension = use_extension("@bedrock-rtl//dependency_support/rules_hdl:extension.bzl", "rules_hdl_extension")
use_repo(rules_hdl_extension, "rules_hdl")
```

</details>

If your root module must redirect the `rules_hdl` wrapper, load its extension from the root dependency instead:

```starlark
bazel_dep(name = "rules_hdl", version = "0.0.0", repo_name = "rules_hdl_wrapper_module")

# Add an override only when your root module supplies the rules_hdl wrapper.
local_path_override(
    module_name = "rules_hdl",
    path = "<path-to-rules-hdl-wrapper>",
)

rules_hdl_extension = use_extension("@rules_hdl_wrapper_module//:extension.bzl", "rules_hdl_extension")
use_repo(rules_hdl_extension, "rules_hdl")
```

> Only the root module can apply module overrides. If `rules_hdl` is available from your configured Bazel registries, no override is needed.

Then suppose your design contains this SystemVerilog module, `datapath_join.sv`:

<details>
<summary><code>datapath_join.sv</code></summary>

```systemverilog
// An example design using two Bedrock-RTL modules: br_flow_reg_fwd and br_flow_join.
//
// Joins two or more equal-width datapaths into a single output datapath.
// Uses ready/valid protocol on all flows.
// Push-side is registered.

`include "br_asserts.svh"

module datapath_join #(
    parameter int NumFlows = 2,  // must be at least 2
    parameter int WidthPerFlow = 32  // must be at least 1
) (
    input logic clk,
    input logic rst,
    output logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic [NumFlows-1:0][WidthPerFlow-1:0] push_data,
    input logic pop_ready,
    output logic pop_valid,
    output logic [(NumFlows*WidthPerFlow)-1:0] pop_data
);

  `BR_ASSERT_STATIC(numflows_gte_2_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(widthperflow_gte_1_a, WidthPerFlow >= 1)

  logic [NumFlows-1:0] inter_ready;
  logic [NumFlows-1:0] inter_valid;
  logic [NumFlows-1:0][WidthPerFlow-1:0] inter_data;

  for (genvar i = 0; i < NumFlows; i++) begin : gen_regs
    br_flow_reg_fwd #(
        .Width(WidthPerFlow)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(push_ready[i]),
        .push_valid(push_valid[i]),
        .push_data (push_data[i]),
        .pop_ready (inter_ready[i]),
        .pop_valid (inter_valid[i]),
        .pop_data  (inter_data[i])
    );
  end

  br_flow_join #(
      .NumFlows(NumFlows)
  ) br_flow_join (
      .clk,
      .rst,
      .push_ready(inter_ready),
      .push_valid(inter_valid),
      .pop_ready (pop_ready),
      .pop_valid (pop_valid)
  );

  assign pop_data = inter_data;  // direct concat

endmodule : datapath_join
```

</details>

Its `BUILD.bazel` can declare the Bedrock dependencies and add an open-source elaboration test:

<details>
<summary><code>BUILD.bazel</code></summary>

```starlark
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_elab_test")
load("@rules_hdl//verilog:providers.bzl", "verilog_library")

package(default_visibility = ["//visibility:private"])

verilog_library(
    name = "datapath_join",
    srcs = ["datapath_join.sv"],
    deps = [
        "@bedrock-rtl//flow/rtl:br_flow_join",
        "@bedrock-rtl//flow/rtl:br_flow_reg_fwd",
        "@bedrock-rtl//macros:br_asserts",
    ],
)

verilog_elab_test(
    name = "datapath_join_elab_test",
    tool = "slang",
    defines = ["BR_ASSERT_ON"],
    deps = [":datapath_join"],
)

```

</details>

This example uses Slang, which is part of the public toolchain. Add lint or multi-tool test suites when your project configures the required tool plugins; see [DEVELOPING.md](DEVELOPING.md).

### Package sources or generate a file list

If your project does not use Bazel, clone Bedrock-RTL at the revision you want and package a library target's transitive sources. This command uses `bazel query`, so install Bazel 9.1.0 first.

```shell
git clone https://github.com/xlsynth/bedrock-rtl.git
cd bedrock-rtl
git checkout <pinned-commit>
./package_sources.py //arb/rtl:br_arb_fixed
```

The generated `.tar` contains a `.f` file and the target's transitive SystemVerilog sources and headers. Extract it, then run your simulator or synthesis tool from the extraction directory. The file list starts with the required `macros` include directory. Choose the library target for the module you use; its name is listed in the library's `BUILD.bazel` file.

Pass `--filelist-only` to generate just the checkout-relative `.f` file.

## Explore the libraries

- [RTL Libraries](LIBRARIES.md) lists the public modules, packages, and formal libraries.
- [SystemVerilog Macros](MACROS.md) documents the register, gate, assignment, and helper macros.
- [Assertions](MACROS.md#assertions) explains public, integration, implementation, and formal assertion controls.
- [Bazel Verilog Rules](bazel/verilog_rules.md) documents the rules supplied by this repository. The `verilog_library` rule itself comes from [rules_hdl](https://github.com/hdl/bazel_rules_hdl/blob/main/verilog/providers.bzl).
- [Scripts](SCRIPTS.md) describes the repository's report-generation scripts.

For repository development, see [DEVELOPING.md](DEVELOPING.md). For pull-request
requirements, see [CONTRIBUTING.md](CONTRIBUTING.md).
