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

import argparse
from typing import List, Optional

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


def verilog_lint_test(hdrs: Optional[List[str]], srcs: List[str]) -> bool:
    """Returns True if the the Verilog/SystemVerilog sources pass a lint test; may print to stdout and/or stderr."""
    # TODO: Implement this using your own tool.
    return True


def main():
    parser = argparse.ArgumentParser(description="Test that Verilog or SystemVerilog modules are able to pass lint checks.",
                                     allow_abbrev=False,
    )
    parser.add_argument("--hdr",
                        type=argparse.FileType("r"),
                        nargs="*",
                        default=[],
                        help="Verilog headers (.vh) or SystemVerilog headers (.svh) to include. "
                             "Can be specified multiple times.",
    )
    parser.add_argument("srcs",
                        type=argparse.FileType("r"),
                        nargs="+",
                        help="One or more Verilog (.h) or SystemVerilog (.sv) source files",
    )
    args = parser.parse_args()

    hdrs = [hdr.name for hdr in args.hdr]
    srcs = [src.name for src in args.srcs]

    check_each_filename_suffix(hdrs, [".vh", ".svh"])
    check_each_filename_suffix(srcs, [".v", ".sv"])

    exit(0) if verilog_lint_test(hdrs, srcs) else exit(1)


if __name__ == "__main__":
    main()
