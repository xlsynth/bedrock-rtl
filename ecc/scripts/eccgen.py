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
from ecc.scripts.hsiao_secded import hsiao_secded_code
import numpy as np


def main():
    parser = argparse.ArgumentParser(description="Error Correction Code Generator")
    parser.add_argument(
        "--scheme",
        type=str,
        choices=["hsiao_secded"],
        required=True,
        help="The error correction code scheme to use (e.g., hsiao_secded)",
    )
    parser.add_argument(
        "--k", type=int, required=True, help="The number of data bits (k)"
    )
    parser.add_argument(
        "--print0",
        action="store_true",
        help="Print 0s in the outputs (otherwise, leave blanks instead).",
    )
    parser.add_argument(
        "--generator-matrix-output",
        "--G",
        type=argparse.FileType("w"),
        required=False,
        help="The output file to write the generator matrix to",
    )
    parser.add_argument(
        "--parity-check-matrix-output",
        "--H",
        type=argparse.FileType("w"),
        required=False,
        help="The output file to write the parity check matrix to",
    )

    args = parser.parse_args()

    if args.scheme == "hsiao_secded":
        r, n, H, G = hsiao_secded_code(args.k)
        print(f"Number of data bits (k): {args.k}")
        print(f"Number of parity bits (r): {r}")
        print(f"Total number of bits (n): {n}\n")

        # Convert matrices to strings without ellipses
        H_str = np.array2string(
            H, separator=", ", threshold=np.inf, max_line_width=np.inf
        ).replace("0", " " if args.print0 else "0")
        G_str = np.array2string(
            G, separator=", ", threshold=np.inf, max_line_width=np.inf
        ).replace("0", " " if args.print0 else "0")

        print("\nGenerator Matrix G:")
        print(G_str)
        if args.generator_matrix_output:
            args.generator_matrix_output.write(G_str)
        print("\nParity-Check Matrix H:")
        print(H_str)
        if args.parity_check_matrix_output:
            args.parity_check_matrix_output.write(H_str)


if __name__ == "__main__":
    main()
