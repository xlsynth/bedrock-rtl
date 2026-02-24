load("@bazel_skylib//rules:diff_test.bzl", "diff_test")
load("@bazel_skylib//rules:write_file.bzl", "write_file")
load("@rules_hdl//verilog:providers.bzl", "verilog_library")

def gen_shared_fifo(
        name,
        sharing_type,
        push_intf,
        pop_intf,
        ext_arbiter,
        ctrl_only,
        template,
        output_file):
    """Generates a shared FIFO controller file from the template.

    Args:
      name: The name of the generated file.
      sharing_type: The type of sharing to use for the FIFO controller. ("dynamic" or "pseudo-static")
      push_intf: The interface type for the push side. ("credit" or "ready")
      pop_intf: The interface type for the pop side. ("credit" or "ready")
      ext_arbiter: Whether to generate with external arbiter interface.
      ctrl_only: Whether to generate only the controller module.
      template: The path to the Jinja2 template file.
      output_file: The path to the generated file.
    """
    command = """$(execpath //fifo/rtl/fifo_codegen) \
    --shared \
    --sharing-type {sharing_type} \
    --push-intf {push_intf} \
    --pop-intf {pop_intf} \
    --template $(location {template}) \
    --output-file $(@D)/{output_file}""".format(
        sharing_type = sharing_type,
        push_intf = push_intf,
        pop_intf = pop_intf,
        template = template,
        output_file = output_file,
    )
    if ext_arbiter:
        command += " --ext-arbiter"
    if ctrl_only:
        command += " --ctrl-only"

    native.genrule(
        name = name,
        srcs = [template],
        tools = ["//fifo/rtl/fifo_codegen"],
        outs = [output_file],
        cmd = command,
    )

def shared_fifo_verilog_library(
        name,
        sharing_type,
        push_intf,
        pop_intf,
        ext_arbiter,
        ctrl_only,
        template,
        src,
        **kwargs):
    """Generates a shared FIFO controller Verilog library from the template.

    Args:
      name: The name of the generated Verilog library.
      sharing_type: The type of sharing to use for the FIFO controller. ("dynamic" or "pseudo-static")
      push_intf: The interface type for the push side. ("credit" or "ready")
      pop_intf: The interface type for the pop side. ("credit" or "ready")
      ext_arbiter: Whether to generate with external arbiter interface.
      ctrl_only: Whether to generate only the controller module.
      template: The path to the Jinja2 template file.
      src: The source file for the checked in golden.
      **kwargs: Additional keyword arguments to pass to the verilog_library rule.
    """
    gen_shared_fifo(
        name = "gen_" + name + "_sv",
        sharing_type = sharing_type,
        push_intf = push_intf,
        pop_intf = pop_intf,
        ext_arbiter = ext_arbiter,
        ctrl_only = ctrl_only,
        template = template,
        output_file = "gen_" + name + ".sv",
    )
    native.genrule(
        name = name + "_formatted",
        srcs = [":gen_" + name + "_sv"],
        outs = ["gen_" + name + "_formatted.sv"],
        cmd = """
        verible-verilog-format $(location :gen_{name}_sv) > $(@D)/gen_{name}_formatted.sv
        """.format(name = name),
    )
    verilog_library(
        name = name,
        srcs = [src],
        **kwargs
    )
    write_file(
        name = "gen_update_" + name,
        out = "update_" + name + ".sh",
        content = [
            "#!/usr/bin/env bash",
            "cd $BUILD_WORKSPACE_DIRECTORY",
            "cp -fv bazel-bin/fifo/rtl/gen_" + name + "_formatted.sv fifo/rtl/" + src,
        ],
    )
    native.sh_binary(
        name = "update_" + name,
        srcs = [":update_" + name + ".sh"],
        data = [
            ":gen_" + name + "_formatted.sv",
            src,
        ],
        tags = ["update_golden"],
    )
    diff_test(
        name = name + "_diff_test",
        failure_message = """
            Golden //fifo/rtl:{name}.sv does not match the generated code.
            Please run `bazel run //fifo/rtl:update_{name}` to automatically update the golden.
        """,
        file1 = src,
        file2 = ":gen_" + name + "_formatted.sv",
        tags = ["check_golden"],
    )
