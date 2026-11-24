# SPDX-License-Identifier: Apache-2.0

"""Write README badges into a fresh or restored Pages site on a hosted runner.

    python3.12 python/ci/pages_badges.py site
    python3.12 python/ci/pages_badges.py site --restored
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess

PUBLIC = ("python", "stardoc", "slang", "verilator")
PRIVATE = ("ascentlint", "vcs")


def suite_badge(counts: object, failure_code: int) -> tuple[str, str]:
    if counts == "incomplete":
        return "incomplete", "lightgrey"
    if isinstance(counts, str) and re.fullmatch(
        r"[0-9]{1,9}/[0-9]{1,9}/[0-9]{1,3}", counts
    ):
        passed, total, code = map(int, counts.split("/"))
        if 0 < total and passed <= total and code <= 255:
            if code == 0 and passed == total:
                return f"{passed} of {total} passing", "brightgreen"
            if code == failure_code and passed < total:
                return f"{passed} of {total} passing", "red"
            return "incomplete", "lightgrey"
    return "unavailable", "lightgrey"


def private_counts() -> dict:
    if os.environ.get("PRIVATE_COUNTS_READY") == "true":
        path = Path(os.environ["RUNNER_TEMP"]) / "badge-counts/proprietary-counts.json"
        try:
            data = json.loads(path.read_text())
            if isinstance(data, dict):
                return data
        except (OSError, ValueError):
            pass
        print("::warning::Proprietary badge counts are unavailable.")
    return {}


def write_badges(site: Path, restored: bool) -> None:
    for name in ("index.html", "coverage/index.html"):
        path = site / name
        if not path.is_file() or not path.stat().st_size:
            raise ValueError(f"Missing or empty dashboard file {name}")

    badges = site / "badges"
    badges.mkdir(exist_ok=True)

    def badge(name, label, message, color):
        data = dict(schemaVersion=1, label=label, message=message, color=color)
        (badges / f"{name}.json").write_text(json.dumps(data))

    run = f"#{os.environ['GITHUB_RUN_NUMBER']} ({os.environ['GITHUB_SHA'][:7]})"
    report = run
    if restored:
        report = json.loads((badges / "report.json").read_text())["message"]
        if not isinstance(report, str) or not re.fullmatch(
            r"#[1-9][0-9]* \([0-9a-f]{7}\)", report
        ):
            raise ValueError("Invalid report source")
        # A restored dashboard can still contain the retired elaboration badge.
        (badges / "verific.json").unlink(missing_ok=True)

    badge("run", "CI snapshot", run, "blue")
    badge("report", "Report", report, "blue")
    rtl = subprocess.check_output(["git", "ls-files", "-z", ":(glob)**/rtl/**/*.sv"])
    badge("rtl", "rtl files", str(rtl.count(b"\0")), "purple")
    # The public aggregator returns 1 on failure. Private suites use Bazel's
    # exit code 3 for failed tests. Other failures can leave partial results.
    for name in PUBLIC:
        badge(name, name, *suite_badge(os.environ.get(name.upper() + "_COUNTS"), 1))
    private = private_counts()
    for name in PRIVATE:
        badge(name, name, *suite_badge(private.get(name), 3))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("--restored", action="store_true")
    args = parser.parse_args()
    write_badges(args.site, args.restored)
