# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

# import unittest library
import unittest

from parameterized import parameterized

from python.regression_gen.regression_gen_lib import Job
from python.regression_gen.regression_gen_lib import render_yaml


class RenderYamlTest(unittest.TestCase):
    """Basic sanity-checks for :pyfunc:`render_yaml`."""

    @parameterized.expand(
        [
            (
                "single_job",
                [Job(name="fpv_core", path="//bedrock/fpv:core", block="core")],
                "jg_fpv_core",
                "fpv_core",
            ),
            (
                "two_jobs_two_blocks",
                [
                    Job(name="fpv_core", path="//bedrock/fpv:core", block="core"),
                    Job(name="fpv_dma", path="//bedrock/fpv:dma", block="dma"),
                ],
                "jg_fpv_dma",
                "fpv_dma",
            ),
        ]
    )
    def test_render_contains_expected_strings(
        self, _name: str, jobs: list[Job], expected_flow: str, expected_job: str
    ) -> None:
        yaml_text = render_yaml(jobs)

        # The rendered document should contain at least these identifiers.
        assert expected_flow in yaml_text, yaml_text
        assert expected_job in yaml_text, yaml_text

        # Each job should show up exactly once in the *jobs* section.
        assert yaml_text.count(f"- name: {expected_job}") == 1
