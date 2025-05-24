"""Helper library for generating regression YAML files.

This library is intentionally kept lightweight so that it can be used in
Bazel rules, standalone Python scripts, or unit-tests.

Typical usage
-------------
>>> from regression_gen_lib import Job, render_yaml
>>> jobs = [
...     Job(name="fpv_core", path="//bedrock/fpv:core", block="core"),
...     Job(name="fpv_dma",  path="//bedrock/fpv:dma",  block="dma"),
... ]
>>> yaml_text = render_yaml(jobs)
>>> print(yaml_text)
"""

from dataclasses import asdict
from dataclasses import dataclass
from pathlib import Path
from typing import List, Sequence

from jinja2 import Environment
from jinja2 import FileSystemLoader
from jinja2 import select_autoescape
from jinja2 import Template

# ----------------------------------------------------------------------------
# Data model
# ----------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Job:
    """A single job description.

    Attributes
    ----------
    name
        Human-readable job name.
    path
        Bazel target (or filesystem path) that should be placed under
        ``bazel_sandbox.path`` in the rendered YAML.
    block
        Bedrock block identifier (used to decide which *flow* the job will
        invoke).
    """

    name: str
    path: str
    block: str


# ----------------------------------------------------------------------------
# Template handling helpers
# ----------------------------------------------------------------------------

_TEMPLATE_FILENAME = "regression.yaml.j2"
_TEMPLATE_DIR = Path(__file__).with_suffix("").parent  # directory of this file
_DEFAULT_TEMPLATE_PATH = _TEMPLATE_DIR / _TEMPLATE_FILENAME

_ENV = Environment(
    loader=FileSystemLoader(str(_TEMPLATE_DIR)),  # avoid Path for py<3.12
    autoescape=select_autoescape(enabled_extensions=()),  # disable YAML escaping
    trim_blocks=True,
    lstrip_blocks=True,
)
# Cache the template – re-loading from disk every call is not necessary.
_TEMPLATE_CACHE: dict[str, Template] = {}


def _load_template(path: Path | str | None = None) -> Template:
    """Return the compiled Jinja2 template.

    Parameters
    ----------
    path
        Optional custom path.  If *None*, the built-in template bundled with
        the package (``regression.yaml.j2``) is used.
    """

    template_path = Path(path) if path is not None else _DEFAULT_TEMPLATE_PATH

    # Use the absolute path string as the cache key to uniquely identify the
    # template even if relative paths differ.
    cache_key = str(template_path.resolve())
    if cache_key not in _TEMPLATE_CACHE:
        # When the user passes in a custom file, create a dedicated loader for
        # its directory so that any ``include`` or ``import_yaml`` statements
        # can still work relative to that file.
        if template_path != _DEFAULT_TEMPLATE_PATH:
            env = Environment(
                loader=FileSystemLoader(str(template_path.parent)),
                autoescape=select_autoescape(enabled_extensions=()),
                trim_blocks=True,
                lstrip_blocks=True,
            )
            _TEMPLATE_CACHE[cache_key] = env.get_template(template_path.name)
        else:
            _TEMPLATE_CACHE[cache_key] = _ENV.get_template(_TEMPLATE_FILENAME)

    return _TEMPLATE_CACHE[cache_key]


# ----------------------------------------------------------------------------
# Public API
# ----------------------------------------------------------------------------


def render_yaml(
    jobs: Sequence[Job | dict],
    *,
    project: str = "bedrock",
    description: str = "Bedrock regression.",
    flow_name: str = "flow",
    default_timeout_mins: int = 1440,
    default_cpus_per_task: int = 4,
    default_mem_mb: int = 8192,
    template_path: str | Path | None = None,
    default_invocation_timeout_mins: int = 1440,
) -> str:
    """Render the regression YAML for the given jobs.

    Parameters
    ----------
    jobs
        Sequence of :class:`Job` instances **or** plain dictionaries that
        provide at least the keys ``name``, ``path``, and ``block``.
    project
        Used to fill ``project`` in the *invocation_defaults* section.
    description
        Used to fill ``description`` in the *invocation_defaults* section.
    flow_name
        Used to fill ``name`` in the *flow_defaults* section.
    default_timeout_mins
        Used to fill ``timeout_mins`` in the *flow_defaults* section.
    default_cpus_per_task
        Used inside the *flow_defaults*->``environment.slurm`` stanza.
    default_mem_mb
        Same purpose as *default_cpus_per_task*.
    template_path
        Optional path to *override* the default Jinja2 template.
    default_invocation_timeout_mins
        Used to fill ``timeout_mins`` in the *invocation_defaults* section.

    Returns
    -------
    str
        Rendered YAML document as a Python string (with a trailing newline).
    """

    # Convert dataclass instances to plain dicts for Jinja2 (makes the template
    # code simpler and avoids surprises with attribute access).
    job_dicts: List[dict] = [asdict(j) if isinstance(j, Job) else dict(j) for j in jobs]

    if not job_dicts:
        raise ValueError("Job list must contain at least one element.")

    # Unique blocks – preserve deterministic ordering for reproducibility.
    blocks = sorted({job["block"] for job in job_dicts})

    context = {
        "jobs": job_dicts,
        "blocks": blocks,
        "project": project,
        "description": description,
        "flow_name": flow_name,
        "default_timeout_mins": default_timeout_mins,
        "default_cpus_per_task": default_cpus_per_task,
        "default_mem_mb": default_mem_mb,
        "default_invocation_timeout_mins": default_invocation_timeout_mins,
    }

    template = _load_template(template_path)
    rendered = template.render(**context)

    # Ensure newline at EOF for POSIX friendliness.
    return rendered.rstrip() + "\n"
