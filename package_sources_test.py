# SPDX-License-Identifier: Apache-2.0

import tarfile
import tempfile
import unittest
from pathlib import Path

import package_sources


class PackageSourcesTest(unittest.TestCase):
    def test_create_package_has_root_project_filelist_and_top(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "rtl").mkdir()
            (root / "rtl" / "top.sv").write_text(
                "module top; endmodule\n", encoding="utf-8"
            )
            package = root / "sources.tar"

            package_sources.create_package(
                package,
                root,
                ["./rtl/top.sv"],
                "top",
            )

            with tarfile.open(package) as archive:
                self.assertEqual(
                    sorted(archive.getnames()),
                    ["project.f", "rtl", "rtl/top.sv"],
                )
                project_filelist = archive.extractfile("project.f")
                self.assertIsNotNone(project_filelist)
                assert project_filelist is not None
                self.assertEqual(
                    project_filelist.read().decode(),
                    "--top top\n+incdir+./macros\n./rtl/top.sv\n",
                )


if __name__ == "__main__":
    unittest.main()
