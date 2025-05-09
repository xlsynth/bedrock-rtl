# Copyright 2025 The Bedrock-RTL Authors
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

load("@rules_hdl//verilog:providers.bzl", "verilog_library")
load("//bazel:br_verilog.bzl", "br_verilog_sim_test_tools_suite")
load("//bazel:verilog.bzl", "verilog_elab_test")

verilog_library(
    name = "br_amba_axi_isolate_sub_tb",
    srcs = ["br_amba_axi_isolate_sub_tb.sv"],
    deps = [
        "//amba/rtl:br_amba_axi_isolate_sub",
    ],
)

verilog_elab_test(
    name = "br_amba_axi_isolate_sub_tb_elab_test",
    tool = "verific",
    deps = [":br_amba_axi_isolate_sub_tb"],
)

br_verilog_sim_test_tools_suite(
    name = "br_amba_axi_isolate_sub_tb_sim_test_tools_suite",
    tools = ["vcs"],
    waves = True,
    deps = [":br_amba_axi_isolate_sub_tb"],
)

verilog_library(
    name = "br_amba_axi_isolate_mgr_tb",
    srcs = ["br_amba_axi_isolate_mgr_tb.sv"],
    deps = [
        "//amba/rtl:br_amba_axi_isolate_mgr",
    ],
)

verilog_elab_test(
    name = "br_amba_axi_isolate_mgr_tb_elab_test",
    tool = "verific",
    deps = [":br_amba_axi_isolate_mgr_tb"],
)

br_verilog_sim_test_tools_suite(
    name = "br_amba_axi_isolate_mgr_tb_sim_test_tools_suite",
    tools = ["vcs"],
    waves = True,
    deps = [":br_amba_axi_isolate_mgr_tb"],
)
