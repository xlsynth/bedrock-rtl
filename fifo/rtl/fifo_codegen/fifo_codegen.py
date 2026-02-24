# SPDX-License-Identifier: Apache-2.0

import argparse
import jinja2
import subprocess


def verible_verilog_format(unformatted: str) -> str:
    result = subprocess.run(
        ["verible-verilog-format", "-"],
        input=unformatted,
        text=True,
        capture_output=True,
    )
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description="FIFO Codegen")
    parser.add_argument(
        "--shared",
        action="store_true",
        help="Generate shared FIFO controller.",
        default=False,
    )
    parser.add_argument(
        "--sharing-type",
        type=str,
        choices=["dynamic", "pseudo-static"],
        help="The type of sharing to use for the FIFO controller.",
    )
    parser.add_argument(
        "--push-intf",
        type=str,
        choices=["credit", "ready"],
        help="The interface type for the push side.",
    )
    parser.add_argument(
        "--pop-intf",
        type=str,
        choices=["credit", "ready"],
        help="The interface type for the pop side.",
    )
    parser.add_argument(
        "--ext-arbiter",
        action="store_true",
        help="Generate with external arbiter interface.",
    )
    parser.add_argument(
        "--ctrl-only",
        action=argparse.BooleanOptionalAction,
        help="Generate only the controller module.",
        default=False,
    )
    parser.add_argument(
        "--template",
        type=str,
        required=True,
        help="The path to the Jinja2 template file.",
    )
    parser.add_argument(
        "--output-file",
        type=str,
        required=True,
        help="The directory to write the generated files to.",
    )
    args = parser.parse_args()

    dynamic = args.sharing_type == "dynamic"
    push_credit = args.push_intf == "credit"
    pop_credit = args.pop_intf == "credit"
    ext_arbiter = args.ext_arbiter

    with open(args.template, "r") as f:
        template = jinja2.Template(f.read())

    if args.shared:
        module_name = "br_fifo_shared"
        pop_ctrl_module = "br_fifo_shared_pop_ctrl"

        if dynamic:
            module_name += "_dynamic"
            push_ctrl_module = "br_fifo_shared_dynamic_push_ctrl"
            ptr_mgr_module = "br_fifo_shared_dynamic_ptr_mgr"
        else:
            module_name += "_pstatic"
            push_ctrl_module = "br_fifo_shared_pstatic_push_ctrl"
            ptr_mgr_module = "br_fifo_shared_pstatic_ptr_mgr"

        if args.ctrl_only:
            module_name += "_ctrl"
        else:
            module_name += "_flops"

        if push_credit:
            module_name += "_push_credit"
            push_ctrl_module += "_credit"

        if pop_credit:
            module_name += "_pop_credit"
            pop_ctrl_module += "_credit"

        if args.ext_arbiter:
            module_name += "_ext_arbiter"
            pop_ctrl_module += "_ext_arbiter"

        rendered = template.render(
            module_name=module_name,
            push_ctrl_module=push_ctrl_module,
            pop_ctrl_module=pop_ctrl_module,
            ptr_mgr_module=ptr_mgr_module,
            dynamic=dynamic,
            push_credit=push_credit,
            pop_credit=pop_credit,
            ext_arbiter=ext_arbiter,
        )
        formatted = verible_verilog_format(rendered)

        with open(args.output_file, "w") as f:
            f.write(formatted)


if __name__ == "__main__":
    main()
