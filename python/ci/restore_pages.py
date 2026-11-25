# SPDX-License-Identifier: Apache-2.0

"""Restore a deployed public dashboard with `python3.12 restore_pages.py DIRECTORY`."""

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
import zipfile


# The current site is about 10 MiB unpacked. Fail closed on unexpected archives.
MAX_BYTES = 128 * 1024 * 1024


def gh(repo: str, endpoint: str) -> bytes:
    return subprocess.check_output(
        ["gh", "api", f"repos/{repo}/{endpoint}"], timeout=60
    )


def deployed_artifact(repo: str) -> tuple[dict, dict]:
    """Find the exact artifact deployed, even if some other CI job failed."""

    def api(endpoint):
        return json.loads(gh(repo, endpoint))

    for deployment in api("deployments?environment=github-pages&ref=main&per_page=10"):
        statuses = api(f"deployments/{deployment['id']}/statuses")
        success = next((s for s in statuses if s["state"] == "success"), None)
        if not success:
            continue
        match = re.fullmatch(
            rf"https://github\.com/{re.escape(repo)}/actions/runs/(\d+)/job/(\d+)",
            success["log_url"],
        )
        if not match:
            raise ValueError("Pages deployment has no recognizable Actions job")
        run_id, job_id = map(int, match.groups())
        job = api(f"actions/jobs/{job_id}")
        run = api(f"actions/runs/{run_id}")
        if not (
            job["run_id"] == run_id
            and job["head_sha"] == deployment["sha"] == run["head_sha"]
            and job["name"] == "deploy-test-results-pages"
            and job["conclusion"] == "success"
            and run["path"] == ".github/workflows/ci.yml"
            and run["head_repository"]["full_name"] == repo
            and run["head_branch"] == "main"
            and run["event"] in ("push", "workflow_dispatch")
        ):
            raise ValueError("Pages deployment is not from trusted main CI")
        # A deployment job can succeed while skipping the deploy step on a stale SHA.
        # A rerun of just that step can publish a package from an earlier attempt.
        steps = [
            s
            for s in job["steps"]
            if re.fullmatch(r"Deploy (GH pages|github-pages-[1-9][0-9]*)", s["name"])
        ]
        if len(steps) != 1:
            raise ValueError("No unique recognized Pages deploy step")
        step = steps[0]
        if step["conclusion"] != "success":
            continue
        # Before the badge migration all Pages artifacts had the same name.
        name = (
            "github-pages"
            if step["name"] == "Deploy GH pages"
            else step["name"].split()[1]
        )
        artifacts = api(f"actions/runs/{run_id}/artifacts?name={name}")["artifacts"]
        candidates = [
            a
            for a in artifacts
            if a["name"] == name
            and not a["expired"]
            and a["created_at"] <= step["started_at"]
        ]
        # Don't roll back further if the deployed artifact has expired.
        if len(candidates) != 1:
            raise ValueError("No unique retained artifact for the deployed site")
        return run, candidates[0]
    raise ValueError("No recent successful main Pages deployment")


def unpack(data: bytes, destination: Path) -> None:
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        entry = archive.getinfo("artifact.tar")
        if entry.file_size > MAX_BYTES:
            raise ValueError("Oversized Pages archive")
        with archive.open(entry) as file, tarfile.open(fileobj=file, mode="r|") as site:
            for member in site:
                path = Path(member.name)
                if (
                    path.is_absolute()
                    or ".." in path.parts
                    or not (member.isdir() or member.isfile())
                    or member.sparse is not None
                ):
                    raise ValueError("Unsafe Pages archive entry")
                site.extract(member, destination, filter="data")
    for name in ("index.html", "coverage/index.html"):
        path = destination / name
        if not path.is_file() or not path.stat().st_size:
            raise ValueError(f"Missing or empty {name} in restored dashboard")


def restore(repo: str, destination: Path) -> None:
    run, artifact = deployed_artifact(repo)
    if artifact["size_in_bytes"] > MAX_BYTES:
        raise ValueError("Oversized Pages artifact")
    data = gh(repo, f"actions/artifacts/{artifact['id']}/zip")
    if artifact["digest"] != "sha256:" + hashlib.sha256(data).hexdigest():
        raise ValueError("Pages artifact digest mismatch")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as temporary:
        site = Path(temporary) / "site"
        site.mkdir()
        unpack(data, site)
        report = site / "badges/report.json"
        if artifact["name"] == "github-pages" and not report.exists():
            message = f"#{run['run_number']} ({run['head_sha'][:7]})"
            report.parent.mkdir(exist_ok=True)
            report.write_text(json.dumps({"message": message}))
        if not json.loads(report.read_text()).get("message"):
            raise ValueError("Missing dashboard source")
        site.rename(destination)
    print(f"Restored public site from CI #{run['run_number']}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    restore(os.environ["GITHUB_REPOSITORY"], parser.parse_args().destination)
