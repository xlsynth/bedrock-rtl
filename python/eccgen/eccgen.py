# Copyright 2024-2025 The Bedrock-RTL Authors
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
from python.eccgen.hsiao_secded import (
    hsiao_secded_code,
    check_construction,
    G_to_sv,
    syndrome_to_sv,
    H_to_sv,
)
import numpy as np
from jinja2 import Template


def check_filename_extension(filename: str, allowed_extensions: tuple[str]) -> str:
    """Checks if a filename has one of the allowed extensions and returns it as-is."""
    if not filename.endswith(allowed_extensions):
        raise argparse.ArgumentTypeError(
            f"File '{filename}' must have one of the extensions: {allowed_extensions}"
        )
    return filename


def sv_jinja2_file(filename: str) -> str:
    return check_filename_extension(filename, (".sv.jinja2"))


def main():
    parser = argparse.ArgumentParser(description="Error Correction Code Generator")
    parser.add_argument(
        "--scheme",
        type=str,
        choices=["hsiao_secded"],
        required=True,
        help="The error correction code scheme to use (e.g., hsiao_secded)",
    )
    parser.add_argument("--k", type=int, help="The number of data bits (k)")
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
    parser.add_argument(
        "--rtl-encoder-template",
        type=sv_jinja2_file,
        required=False,
        help="The input file containing the Jinja2 SystemVerilog RTL code template for the encoder.",
    )
    parser.add_argument(
        "--rtl-encoder-output",
        type=argparse.FileType("w"),
        required=False,
        help="Dump the encoder implementation for all supported codes to the provided output file.",
    )
    parser.add_argument(
        "--rtl-decoder-template",
        type=sv_jinja2_file,
        required=False,
        help="The input file containing the Jinja2 SystemVerilog RTL code template for the decoder.",
    )
    parser.add_argument(
        "--rtl-decoder-output",
        type=argparse.FileType("w"),
        required=False,
        help="Dump the decoder implementation for all supported codes to the provided output file.",
    )

    args = parser.parse_args()

    if args.scheme == "hsiao_secded":
        if args.k:
            r, n, H, G = hsiao_secded_code(args.k)
            check_construction(G, H)
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

        if args.rtl_encoder_output:
            if not args.rtl_encoder_template:
                raise ValueError(
                    "RTL encoder template file is required to generate the encoder."
                )

            RTL_SUPPORTED_N_K = [
                (8, 4),
                (13, 8),
                (22, 16),
                (39, 32),
                (72, 64),
                (137, 128),
                (266, 256),
                (523, 512),
                (1036, 1024),
            ]
            with open(args.rtl_encoder_template, "r") as template_file:
                template = Template(template_file.read())
                mapping = {}
                for n, k in RTL_SUPPORTED_N_K:
                    r, n, H, G = hsiao_secded_code(k)
                    check_construction(G, H)
                    mapping[f"secded_enc_{n}_{k}"] = G_to_sv(G)
                rendered = template.render(mapping)
                rendered += "\n"
                args.rtl_encoder_output.write(rendered)

        if args.rtl_decoder_output:
            if not args.rtl_decoder_template:
                raise ValueError(
                    "RTL decoder template file is required to generate the decoder."
                )

            RTL_SUPPORTED_N_K = [
                (8, 4),
                (13, 8),
                (22, 16),
                (39, 32),
                (72, 64),
                (137, 128),
                (266, 256),
                (523, 512),
                (1036, 1024),
            ]
            with open(args.rtl_decoder_template, "r") as template_file:
                template = Template(template_file.read())
                mapping = {}
                for n, k in RTL_SUPPORTED_N_K:
                    r, n, H, G = hsiao_secded_code(k)
                    check_construction(G, H)
                    mapping[f"secded_dec_syndrome_{n}_{k}"] = syndrome_to_sv(H)
                    mapping[f"secded_dec_H_{n}_{k}"] = H_to_sv(H)
                rendered = template.render(mapping)
                rendered += "\n"
                args.rtl_decoder_output.write(rendered)

        if not args.k and not args.rtl_encoder_output and not args.rtl_decoder_output:
            raise ValueError(
                "Either k or rtl-encoder-output or rtl-decoder-output must be provided for Hsiao SEC-DED code generation."
            )


if __name__ == "__main__":
    main()
