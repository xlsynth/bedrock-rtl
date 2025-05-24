"""CLI tool that discovers rules with Bazel and emits regression
*regr.yaml* file using `render_yaml`.

This tool is intentionally kept simple and not flexible to support
multiple use cases.

Usage example
-------------
```
python -m python.regression_gen.regression_gen \
    --block core \
    --directory //bedrock/fpv \
    --rule-kind rule_verilog_fpv_sandbox \
    --output regr.yaml
```
"""

import os
from pathlib import Path
import subprocess
import sys

import click

from python.regression_gen.regression_gen_lib import Job
from python.regression_gen.regression_gen_lib import render_yaml

# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------


def _run_bazel_query(expr: str) -> list[str]:
    """Run `bazel query` and return a list of labels (strings)."""

    try:
        completed = subprocess.run(
            [
                "bazel",
                "query",
                "--output=label",
                expr,
            ],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except FileNotFoundError:
        click.echo("ERROR: `bazel` executable not found in PATH.", err=True)
        sys.exit(1)
    except subprocess.CalledProcessError as exc:
        click.echo(exc.stderr, err=True)
        click.echo("ERROR: Bazel query failed.", err=True)
        sys.exit(exc.returncode)

    return [line.strip() for line in completed.stdout.splitlines() if line.strip()]


def _derive_job_from_label(label: str, block: str) -> Job:
    """Convert a Bazel label (e.g., //foo/bar:sandbox) into a Job dataclass."""

    if ":" in label:
        name = label.split(":", 1)[1]
    else:  # Fallback – last path component
        name = Path(label).name

    # Strip trailing '_fpv_sandbox' if present
    if name.endswith("_fpv_sandbox"):
        name = name[: -len("_fpv_sandbox")]

    return Job(name=name, path=label, block=block)


def _get_workspace_root() -> Path:
    """Return the absolute path to Bazel workspace root using `bazel info workspace`."""

    try:
        completed = subprocess.run(
            ["bazel", "info", "workspace"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        return Path(completed.stdout.strip())
    except Exception:  # fall back silently
        return Path.cwd()


def _workspace_relative_dir(dir_label: str) -> Path:
    """Convert a label like '//foo/bar/...' to workspace-relative Path('foo/bar')."""

    path = dir_label[2:]
    if path.endswith("/..."):
        path = path[:-4]
    return Path(path)


def _resolve_output_path(output_str: str | None, *, default_dir_label: str) -> Path:
    """Resolve the final output *file* path according to user rules."""

    workspace_root = _get_workspace_root()

    if output_str is None:
        return workspace_root / _workspace_relative_dir(default_dir_label) / "regr.yaml"

    # Provided output
    p = Path(output_str)

    # Case 1: single file name (no path separators)
    if p.name == output_str and not p.is_absolute():
        return workspace_root / _workspace_relative_dir(default_dir_label) / p.name

    # Case 2: absolute path (file or dir)
    if p.is_absolute():
        if p.suffix:
            return p
        return p / "regr.yaml"

    # Case 3: relative path with separators -> relative to cwd
    cwd_path = Path.cwd() / p
    if p.suffix:
        return cwd_path
    return cwd_path / "regr.yaml"


# -----------------------------------------------------------------------------
# Click CLI
# -----------------------------------------------------------------------------


@click.command(context_settings={"help_option_names": ["-h", "--help"]})
@click.option(
    "--project",
    default="bedrock",
    show_default=True,
    help="Bedrock project name to put in the generated YAML (required).",
)
@click.option(
    "--flow-name",
    default="flow",
    show_default=True,
    help="Flow name to put in the generated YAML (required).",
)
@click.option(
    "--description",
    default="Bedrock regression.",
    show_default=True,
    help="Description to put in the generated YAML (required).",
)
@click.option(
    "--block",
    required=True,
    help="Bedrock block name to put in the generated YAML (required).",
)
@click.option(
    "--directory",
    "-d",
    required=True,
    help="Bazel directory label to search under, e.g. //bedrock/fpv ( '/...' will be appended automatically ).",
)
@click.option(
    "--rule-kind",
    default="rule_verilog_fpv_sandbox",
    show_default=True,
    help="Bazel rule kind to query for.",
)
@click.option(
    "--output",
    "-o",
    type=str,
    help=(
        "Output file or directory.  If it is:  (a) a bare filename, it is written "
        "under --directory;  (b) a relative path containing '/', it is resolved "
        "relative to the current working directory;  (c) an absolute path, it is "
        "used as-is.  In all cases, if the path points to a directory, the file "
        "'regr.yaml' is appended automatically.  Default: <--directory>/regr.yaml."
    ),
)
@click.option("--default-timeout-mins", default=30, show_default=True, type=int)
@click.option("--default-cpus-per-task", default=4, show_default=True, type=int)
@click.option("--default-mem-mb", default=32768, show_default=True, type=int)
@click.option(
    "--default-invocation-timeout-mins", default=1440, show_default=True, type=int
)
@click.option(
    "--dry-run",
    is_flag=True,
    help="Only list discovered targets and show the rendered YAML on stdout without writing the file.",
)
def cli(
    project: str,
    flow_name: str,
    description: str,
    block: str,
    directory: str,
    rule_kind: str,
    output: str | None,
    default_timeout_mins: int,
    default_cpus_per_task: int,
    default_mem_mb: int,
    default_invocation_timeout_mins: int,
    dry_run: bool,
) -> None:
    """Discover FPV sandbox targets and generate *regr.yaml*."""

    # Normalise directory label
    dir_label = directory.rstrip("/")
    if not dir_label.startswith("//"):
        click.echo("ERROR: --directory must start with '//' (Bazel label)", err=True)
        sys.exit(1)

    query_expr = f'kind("{rule_kind} rule", {dir_label}/...)'
    # click.echo(f"Running Bazel query: {query_expr}")

    labels: list[str] = _run_bazel_query(query_expr)
    if not labels:
        click.echo("No matching targets found. Exiting.", err=True)
        sys.exit(2)

    jobs = [_derive_job_from_label(label, block) for label in sorted(labels)]

    yaml_text = render_yaml(
        jobs,
        project=project,
        flow_name=flow_name,
        description=description,
        default_timeout_mins=default_timeout_mins,
        default_cpus_per_task=default_cpus_per_task,
        default_mem_mb=default_mem_mb,
        default_invocation_timeout_mins=default_invocation_timeout_mins,
    )

    if dry_run:
        click.echo("--- YAML output (dry-run) ---")
        click.echo(yaml_text)
        return

    # Resolve output directory
    final_output_path = _resolve_output_path(
        output,
        default_dir_label=dir_label,
    )

    final_output_path.parent.mkdir(parents=True, exist_ok=True)
    final_output_path.write_text(yaml_text, encoding="utf-8")
    click.echo(f"Wrote {len(jobs)} jobs to {final_output_path}")


def main() -> None:  # pragma: no cover – entry-point convenience
    cli()  # pylint: disable=no-value-for-parameter


if __name__ == "__main__":
    # Change the working directory to the original directory if invoked from bazel run, e.g.
    #   bazel run :sandbox_cli -- example/testlist_tbA.yaml tbA_test
    # This is to allow the yaml file to be found via relative path to the user's working directory.
    if (
        "BUILD_WORKING_DIRECTORY" in os.environ
        and os.environ["BUILD_WORKING_DIRECTORY"] != ""
    ):
        os.chdir(os.environ["BUILD_WORKING_DIRECTORY"])
    main()
