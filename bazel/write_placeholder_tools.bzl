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

"""Placeholder tool code generation for Verilog/SystemVerilog lint and elaboration tests."""

_PLACEHOLDER_VERILOG_ELAB_TEST_TOOL_CONTENT = '''#!/usr/bin/env python3.12

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

"""Auto-generated code: placeholder Python implementation of the verilog_elab_test tool API."""

import argparse
from typing import Dict, List, Optional

def check_each_filename_suffix(filenames: List[str], suffices: List[str]) -> None:
    """Raises ValueError if there is any filename in the list that doesn't end with any of the expected suffices."""
    for filename in filenames:
        match = False
        for suffix in suffices:
            if filename.endswith(suffix):
                match = True
                break
        if not match:
            raise ValueError(f"Expected filename to end with any of {suffices}: {filename}")


def verilog_elab_test(hdrs: Optional[List[str]], defines: Optional[List[str]], params: Optional[Dict[str, str]], top: Optional[str], srcs: List[str]) -> bool:
    """Returns True if the top-level Verilog or SystemVerilog module is able to elaborate; may print to stdout and/or stderr."""
    # TODO: Implement this using your own tool.
    print("NOT IMPLEMENTED: Test vacuously passes.")
    return True

def parse_params(parser: argparse.ArgumentParser, params: Optional[List[str]]) -> Dict[str, str]:
    """Parses parameters into a dict; raises an error if any of the parameters are not in the expected KEY=VALUE format."""
    params_dict = {}
    if params:
        for item in params:
            if '=' in item:
                key, value = item.split('=', 1)
                params_dict[key] = value
            else:
                parser.error(f"Invalid format for --param '{item}'. Expected KEY=VALUE.")
    return params_dict

def main():
    parser = argparse.ArgumentParser(description="Test that a top-level Verilog or SystemVerilog module is able to elaborate.",
                                     allow_abbrev=False,
    )
    parser.add_argument("--top",
                        type=str,
                        help="Top module",
    )
    parser.add_argument("--hdr",
                        type=argparse.FileType("r"),
                        action="append",
                        default=[],
                        help="Verilog header (.vh) or SystemVerilog header (.svh) to include. "
                             "Can be specified multiple times.",
    )
    parser.add_argument("--define",
                        type=str,
                        action="append",
                        default=[],
                        help="Verilog/SystemVerilog preprocessor define to use in compilation. Can be specified multiple times.",
    )
    parser.add_argument("--param",
                        action="append",
                        metavar="KEY=VALUE",
                        default=[],
                        help="Verilog/SystemVerilog module parameter key-value pair for the top module. Can be specified multiple times.",
    )
    parser.add_argument("srcs",
                        type=argparse.FileType("r"),
                        nargs="+",
                        help="One or more Verilog (.h) or SystemVerilog (.sv) source files",
    )

    args = parser.parse_args()

    hdrs = [hdr.name for hdr in args.hdr]
    srcs = [src.name for src in args.srcs]
    defines = args.define
    params = parse_params(parser, args.param)

    check_each_filename_suffix(hdrs, [".vh", ".svh"])
    check_each_filename_suffix(srcs, [".v", ".sv"])

    exit(0) if verilog_elab_test(hdrs=hdrs, defines=defines, params=params, top=args.top, srcs=srcs) else exit(1)


if __name__ == "__main__":
    main()
'''

_PLACEHOLDER_VERILOG_LINT_TEST_TOOL_CONTENT = '''#!/usr/bin/env python3.12
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

"""Auto-generated code: placeholder Python implementation of the verilog_lint_test tool API."""

import argparse
from typing import Dict, List, Optional

def check_each_filename_suffix(filenames: List[str], suffices: List[str]) -> None:
    """Raises ValueError if there is any filename in the list that doesn't end with any of the expected suffices."""
    for filename in filenames:
        match = False
        for suffix in suffices:
            if filename.endswith(suffix):
                match = True
                break
        if not match:
            raise ValueError(f"Expected filename to end with any of {suffices}: {filename}")

def parse_params(parser: argparse.ArgumentParser, params: Optional[List[str]]) -> Dict[str, str]:
    """Parses parameters into a dict; raises an error if any of the parameters are not in the expected KEY=VALUE format."""
    params_dict = {}
    if params:
        for item in params:
            if '=' in item:
                key, value = item.split('=', 1)
                params_dict[key] = value
            else:
                parser.error(f"Invalid format for --param '{item}'. Expected KEY=VALUE.")
    return params_dict

def verilog_lint_test(hdrs: Optional[List[str]], defines: Optional[List[str]], params: Optional[Dict[str, str]], top: Optional[str], srcs: List[str]) -> bool:
    """Returns True if the the Verilog/SystemVerilog sources pass a lint test; may print to stdout and/or stderr."""
    # TODO: Implement this using your own tool.
    print("NOT IMPLEMENTED: Test vacuously passes.")
    return True


def main():
    parser = argparse.ArgumentParser(description="Test that Verilog or SystemVerilog modules are able to pass lint checks.",
                                     allow_abbrev=False,
    )
    parser.add_argument("--top",
                        type=str,
                        help="Top module",
    )
    parser.add_argument("--hdr",
                        type=argparse.FileType("r"),
                        action="append",
                        default=[],
                        help="Verilog header (.vh) or SystemVerilog header (.svh) to include. "
                             "Can be specified multiple times.",
    )
    parser.add_argument("--define",
                        type=str,
                        action="append",
                        default=[],
                        help="Verilog/SystemVerilog preprocessor define to use in compilation. Can be specified multiple times.",
    )
    parser.add_argument("--param",
                        action="append",
                        metavar="KEY=VALUE",
                        default=[],
                        help="Verilog/SystemVerilog module parameter key-value pair for the top module. Can be specified multiple times.",
    )
    parser.add_argument("srcs",
                        type=argparse.FileType("r"),
                        nargs="+",
                        help="One or more Verilog (.h) or SystemVerilog (.sv) source files",
    )
    args = parser.parse_args()

    hdrs = [hdr.name for hdr in args.hdr]
    srcs = [src.name for src in args.srcs]
    defines = args.define
    params = parse_params(parser, args.param)

    check_each_filename_suffix(hdrs, [".vh", ".svh"])
    check_each_filename_suffix(srcs, [".v", ".sv"])

    exit(0) if verilog_lint_test(hdrs=hdrs, defines=defines, params=params, top=args.top, srcs=srcs) else exit(1)


if __name__ == "__main__":
    main()
'''

def _write_placeholder_tool(ctx, filename, content):
    """Writes a placeholder Python implementation of the verilog_elab_test tool API."""
    file = ctx.actions.declare_file(filename)
    ctx.actions.write(
        output = file,
        content = content,
        is_executable = True,
    )
    return file

def write_placeholder_verilog_elab_test_tool(ctx):
    return _write_placeholder_tool(ctx, "placeholder_verilog_elab_test.py", _PLACEHOLDER_VERILOG_ELAB_TEST_TOOL_CONTENT)

def write_placeholder_verilog_lint_test_tool(ctx):
    return _write_placeholder_tool(ctx, "placeholder_verilog_lint_test.py", _PLACEHOLDER_VERILOG_LINT_TEST_TOOL_CONTENT)
