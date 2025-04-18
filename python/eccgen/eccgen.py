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

RTL_SUPPORTED_N_K = [
    (8, 4),
    (13, 8),
    (16, 11),
    (22, 16),
    (32, 26),
    (39, 32),
    (64, 57),
    (72, 64),
    (128, 120),
    (137, 128),
    (256, 247),
    (266, 256),
]


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

    did_something = False
    if args.scheme == "hsiao_secded":
        if args.k:
            r, n, H, G = hsiao_secded_code(args.k)
            check_construction(G, H)

            file_header = "\n".join(
                [
                    f"Number of data bits (k): {args.k}",
                    f"Number of parity bits (r): {r}",
                    f"Number of codeword bits (n): {n}",
                ]
            )

            # Convert matrices to strings without ellipses
            G_str = np.array2string(
                G, separator=", ", threshold=np.inf, max_line_width=np.inf
            ).replace("0", " " if args.print0 else "0")
            H_str = np.array2string(
                H, separator=", ", threshold=np.inf, max_line_width=np.inf
            ).replace("0", " " if args.print0 else "0")

            if args.generator_matrix_output:
                args.generator_matrix_output.write(
                    file_header + "\nG =\n" + G_str + "\n"
                )
            if args.parity_check_matrix_output:
                args.parity_check_matrix_output.write(
                    file_header + "\nH =\n" + H_str + "\n"
                )
            did_something = True

        if args.rtl_encoder_output or args.rtl_decoder_output:
            codes = {}
            for n, k in RTL_SUPPORTED_N_K:
                r, n, H, G = hsiao_secded_code(k)
                check_construction(G, H)
                codes[k] = (r, n, H, G)

            if args.rtl_encoder_output:
                if not args.rtl_encoder_template:
                    raise ValueError(
                        "RTL encoder template file is required to generate the encoder."
                    )
                with open(args.rtl_encoder_template, "r") as template_file:
                    template = Template(template_file.read())
                    mapping = {}
                    for k in codes:
                        r, n, H, G = codes[k]
                        mapping[f"secded_enc_{n}_{k}"] = G_to_sv(G)
                    rendered = template.render(mapping)
                    rendered += "\n"
                    args.rtl_encoder_output.write(rendered)

            if args.rtl_decoder_output:
                if not args.rtl_decoder_template:
                    raise ValueError(
                        "RTL decoder template file is required to generate the decoder."
                    )

                with open(args.rtl_decoder_template, "r") as template_file:
                    template = Template(template_file.read())
                    mapping = {}
                    for k in codes:
                        r, n, H, G = codes[k]
                        mapping[f"secded_dec_syndrome_{n}_{k}"] = syndrome_to_sv(H)
                        mapping[f"secded_dec_H_{n}_{k}"] = H_to_sv(H)
                    rendered = template.render(mapping)
                    rendered += "\n"
                    args.rtl_decoder_output.write(rendered)

            did_something = True

        if not did_something:
            raise ValueError(
                "Either --k or --rtl-encoder-output or --rtl-decoder-output must be provided for Hsiao SEC-DED code generation."
            )


if __name__ == "__main__":
    main()
