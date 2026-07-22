#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Package a Bazel Verilog library target's sources and generated filelist."""

import argparse
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Package a Bazel Verilog library target's transitive SystemVerilog "
            "sources and headers with a generated filelist."
        )
    )
    parser.add_argument(
        "--filelist-only",
        action="store_true",
        help="generate only the checkout-relative filelist",
    )
    parser.add_argument(
        "-o",
        "--output-file",
        type=Path,
        help="explicit output filename; overrides the generated name",
    )
    parser.add_argument("target", help="Bazel Verilog library target")
    parser.add_argument(
        "output_path",
        nargs="?",
        type=Path,
        help="directory for the generated output (default: current directory)",
    )
    args = parser.parse_args()
    if args.output_file is not None and args.output_path is not None:
        parser.error("specify either an output path or --output-file, not both")
    return args


def sanitized_target(target: str) -> str:
    return target.replace("//", "_").replace("/", "_").replace(":", "_")


def query_source_paths(target: str) -> list[str]:
    try:
        result = subprocess.run(
            [
                "bazel",
                "query",
                f"kind('source file', deps({target}))",
                "--output=label",
            ],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        )
    except subprocess.CalledProcessError as error:
        print(f"Failed to query Bazel target: {target}", file=sys.stderr)
        raise SystemExit(error.returncode) from error

    return [
        "." + label.replace("//", "/").replace(":", "/")
        for label in result.stdout.splitlines()
        if label.endswith((".sv", ".svh"))
    ]


def top_module(target: str) -> str:
    return target.rsplit(":", 1)[-1]


def write_filelist(path: Path, source_paths: list[str], top: str) -> None:
    path.write_text(
        f"--top {top}\n"
        "+incdir+./macros\n" + "\n".join(source_paths) + ("\n" if source_paths else ""),
        encoding="utf-8",
    )


def create_package(
    package_path: Path,
    source_root: Path,
    source_paths: list[str],
    top: str,
) -> None:
    with tempfile.TemporaryDirectory(prefix="package_sources_") as staging_directory:
        staging_path = Path(staging_directory)
        write_filelist(staging_path / "project.f", source_paths, top)
        for source_path in source_paths:
            relative_path = Path(source_path).relative_to(".")
            destination = staging_path / relative_path
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_root / relative_path, destination)

        with tarfile.open(package_path, "w") as archive:
            for path in sorted(staging_path.iterdir()):
                archive.add(path, arcname=path.name)


def main() -> None:
    args = parse_args()
    target_name = sanitized_target(args.target)
    top = top_module(args.target)
    output_directory = args.output_path or Path(".")
    filelist_name = f"filelist_paths_{target_name}.f"
    source_paths = query_source_paths(args.target)

    if args.filelist_only:
        filelist_path = args.output_file or output_directory / filelist_name
        filelist_path.parent.mkdir(parents=True, exist_ok=True)
        write_filelist(filelist_path, source_paths, top)
        print(f"File list generated and saved to {filelist_path}")
        return

    package_path = (
        args.output_file or output_directory / f"package_sources_{target_name}.tar"
    )
    package_path.parent.mkdir(parents=True, exist_ok=True)
    create_package(package_path, Path.cwd(), source_paths, top)

    print(f"Source package generated and saved to {package_path}")


if __name__ == "__main__":
    main()
