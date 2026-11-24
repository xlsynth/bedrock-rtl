# SPDX-License-Identifier: Apache-2.0

import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from python.ci import restore_pages


def pages_zip(files):
    site = io.BytesIO()
    with tarfile.open(fileobj=site, mode="w") as archive:
        for name, data in files.items():
            entry = tarfile.TarInfo(name)
            entry.size = len(data)
            archive.addfile(entry, io.BytesIO(data))
    result = io.BytesIO()
    with zipfile.ZipFile(result, "w") as archive:
        archive.writestr("artifact.tar", site.getvalue())
    return result.getvalue()


class RestorePagesTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.site = Path(tmp.name) / "site"
        self.repo = "example/rtl"
        self.run = dict(
            path=".github/workflows/ci.yml",
            head_repository={"full_name": self.repo},
            event="push",
            head_branch="main",
            head_sha="a" * 40,
            run_number=23,
            conclusion="failure",
        )
        self.step = dict(
            name="Deploy github-pages-1", conclusion="success", started_at="2026-01-02"
        )
        self.report = b'{"message":"#17 (1234567)"}'
        self.files = {
            "index.html": b"report",
            "coverage/index.html": b"coverage",
            "badges/report.json": self.report,
        }
        self.artifact = dict(
            id=42, name="github-pages-1", created_at="2026-01-01", expired=False
        )
        self.responses = {
            "deployments?environment=github-pages&ref=main&per_page=10": [
                {"id": 1, "sha": self.run["head_sha"]}
            ],
            "deployments/1/statuses": [
                {
                    "state": "success",
                    "log_url": f"https://github.com/{self.repo}/actions/runs/2/job/3",
                }
            ],
            "actions/jobs/3": {
                "name": "deploy-test-results-pages",
                "run_id": 2,
                "head_sha": self.run["head_sha"],
                "conclusion": "success",
                "run_attempt": 2,
                "steps": [self.step],
            },
            "actions/runs/2": self.run,
        }

    def restore(self):
        data = pages_zip(self.files)
        self.artifact.update(
            size_in_bytes=len(data), digest="sha256:" + hashlib.sha256(data).hexdigest()
        )
        self.responses["actions/runs/2/artifacts?name=" + self.artifact["name"]] = {
            "artifacts": [self.artifact]
        }

        def fake_gh(repo, endpoint):
            self.assertEqual(repo, self.repo)
            if endpoint == "actions/artifacts/42/zip":
                return data
            return json.dumps(self.responses[endpoint]).encode()

        with patch.object(restore_pages, "gh", fake_gh):
            restore_pages.restore(self.repo, self.site)

    def test_successful_deploy_on_failed_run_preserves_original_report(self):
        self.restore()
        self.assertEqual((self.site / "badges/report.json").read_bytes(), self.report)
        self.assertEqual((self.site / "coverage/index.html").read_bytes(), b"coverage")

    def test_legacy_site_gets_original_source(self):
        self.step["name"] = "Deploy GH pages"
        self.artifact["name"] = "github-pages"
        del self.files["badges/report.json"]
        self.restore()
        self.assertEqual(
            json.loads((self.site / "badges/report.json").read_text())["message"],
            "#23 (aaaaaaa)",
        )

    def test_rejects_pull_request_run(self):
        self.run["event"] = "pull_request"
        with self.assertRaisesRegex(ValueError, "trusted main"):
            self.restore()
        self.assertFalse(self.site.exists())

    def test_expired_artifact_leaves_destination_untouched(self):
        self.artifact["expired"] = True
        with self.assertRaisesRegex(ValueError, "retained artifact"):
            self.restore()
        self.assertFalse(self.site.exists())

    def test_rejects_unsafe_archive(self):
        self.files["../../escape"] = b"unsafe"
        with self.assertRaisesRegex(ValueError, "Unsafe Pages"):
            self.restore()
        self.assertFalse(self.site.exists())
        self.assertFalse((self.site.parent / "escape").exists())

    def test_rejects_incomplete_site(self):
        del self.files["coverage/index.html"]
        with self.assertRaisesRegex(ValueError, "coverage/index.html"):
            self.restore()
        self.assertFalse(self.site.exists())


if __name__ == "__main__":
    unittest.main()
