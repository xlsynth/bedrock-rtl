# SPDX-License-Identifier: Apache-2.0

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
    deps = [":br_amba_axi_isolate_mgr_tb"],
)

verilog_library(
    name = "br_amba_axi_demux_tb",
    srcs = ["br_amba_axi_demux_tb.sv"],
    deps = [
        "//amba/rtl:br_amba_axi_demux",
    ],
)

verilog_elab_test(
    name = "br_amba_axi_demux_tb_elab_test",
    tool = "verific",
    deps = [":br_amba_axi_demux_tb"],
)

br_verilog_sim_test_tools_suite(
    name = "br_amba_axi_demux_tb_sim_test_tools_suite",
    tools = ["vcs"],
    deps = [":br_amba_axi_demux_tb"],
)
