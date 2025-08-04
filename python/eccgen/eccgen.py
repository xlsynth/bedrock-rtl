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
    G_to_x,
    syndrome_to_sv,
    syndrome_to_x,
    H_to_sv,
    H_to_x,
    MAX_K_FOR_OPTIMAL_ALGORITHM,
)
import numpy as np
from jinja2 import Template
from typing import Optional

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
    (512, 502),
    (523, 512),
    (1024, 1013),
    (1036, 1024),
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


def x_jinja2_file(filename: str) -> str:
    return check_filename_extension(filename, (".x.jinja2"))


def render_encoder_jinja2_template(
    codes, G_codegen, template_file: Optional[str], output_file: str
) -> None:
    if not template_file:
        raise ValueError("Template file is required to generate the encoder.")
    with open(template_file, "r") as template_file:
        template = Template(template_file.read())
        mapping = {}
        for k in codes:
            r, n, H, G = codes[k]
            mapping[f"secded_enc_{n}_{k}"] = G_codegen(G)
        rendered = template.render(mapping)
        rendered += "\n"
        output_file.write(rendered)


def render_decoder_jinja2_template(
    codes, H_codegen, syndrome_codegen, template_file: Optional[str], output_file: str
) -> None:
    if not template_file:
        raise ValueError("Template file is required to generate the decoder.")
    with open(template_file, "r") as template_file:
        template = Template(template_file.read())
        mapping = {}
        for k in codes:
            r, n, H, G = codes[k]
            mapping[f"secded_dec_syndrome_{n}_{k}"] = syndrome_codegen(H)
            mapping[f"secded_dec_H_{n}_{k}"] = H_codegen(H)
        rendered = template.render(mapping)
        rendered += "\n"
        output_file.write(rendered)


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
        "--sv-encoder-template",
        type=sv_jinja2_file,
        required=False,
        help="The input file containing the Jinja2 SystemVerilog RTL code template for the encoder.",
    )
    parser.add_argument(
        "--sv-encoder-output",
        type=argparse.FileType("w"),
        required=False,
        help="Dump the encoder implementation for all supported codes to the provided output file.",
    )
    parser.add_argument(
        "--sv-decoder-template",
        type=sv_jinja2_file,
        required=False,
        help="The input file containing the Jinja2 SystemVerilog RTL code template for the decoder.",
    )
    parser.add_argument(
        "--sv-decoder-output",
        type=argparse.FileType("w"),
        required=False,
        help="Dump the decoder implementation for all supported codes to the provided output file.",
    )
    parser.add_argument(
        "--x-encoder-template",
        type=x_jinja2_file,
        required=False,
        help="The input file containing the Jinja2 DSLX code template for the encoder.",
    )
    parser.add_argument(
        "--x-encoder-output",
        type=argparse.FileType("w"),
        required=False,
        help="Dump the encoder implementation for all supported codes to the provided output file.",
    )
    parser.add_argument(
        "--x-decoder-template",
        type=x_jinja2_file,
        required=False,
        help="The input file containing the Jinja2 DSLX code template for the decoder.",
    )
    parser.add_argument(
        "--x-decoder-output",
        type=argparse.FileType("w"),
        required=False,
        help="Dump the decoder implementation for all supported codes to the provided output file.",
    )

    args = parser.parse_args()

    did_something = False
    if args.scheme == "hsiao_secded":
        if args.k:
            r, n, H, G = hsiao_secded_code(args.k)
            check_construction(
                G,
                H,
                # Code distance check is prohibitively expensive for large k
                check_code_distance=(args.k <= MAX_K_FOR_OPTIMAL_ALGORITHM),
                # Row balance check is omitted for non-optimal constructions
                # since they aren't guaranteed to satisfy the property.
                check_row_balance=(args.k <= MAX_K_FOR_OPTIMAL_ALGORITHM),
            )

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

        codes = {}
        if (
            args.sv_encoder_output
            or args.sv_decoder_output
            or args.x_encoder_output
            or args.x_decoder_output
        ):
            did_something = True
            for n, k in RTL_SUPPORTED_N_K:
                r, n, H, G = hsiao_secded_code(k)
                # Don't bother checking the construction, we already cover all of the RTL
                # supported combinations in hsiao_secded_test.py.
                codes[k] = (r, n, H, G)

        if args.sv_encoder_output:
            render_encoder_jinja2_template(
                codes, G_to_sv, args.sv_encoder_template, args.sv_encoder_output
            )
        if args.sv_decoder_output:
            render_decoder_jinja2_template(
                codes,
                H_to_sv,
                syndrome_to_sv,
                args.sv_decoder_template,
                args.sv_decoder_output,
            )
        if args.x_encoder_output:
            render_encoder_jinja2_template(
                codes, G_to_x, args.x_encoder_template, args.x_encoder_output
            )
        if args.x_decoder_output:
            render_decoder_jinja2_template(
                codes,
                H_to_x,
                syndrome_to_x,
                args.x_decoder_template,
                args.x_decoder_output,
            )

        if not did_something:
            raise ValueError(
                "One of --k, --sv-encoder-output, --sv-decoder-output, --x-encoder-output or --x-decoder-output must be provided for Hsiao SEC-DED code generation."
            )


if __name__ == "__main__":
    main()
