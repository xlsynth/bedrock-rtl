# Copyright 2024 The Bedrock-RTL Authors
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

"""Abstract base class for Verilog Runner EDA tool plugins to implement."""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
import logging
from typing import Dict, List, Optional

from util import dump_file, write_and_dump_file, to_filelist


@dataclass
class EdaTool(ABC):
    hdrs: List[str] = field(default_factory=list)
    defines: List[str] = field(default_factory=list)
    params: Dict[str, str] = field(default_factory=dict)
    opts: List[str] = field(default_factory=list)
    srcs: List[str] = field(default_factory=list)
    top: str = field(default_factory=str)
    logfile: str = field(default_factory=str)
    tclfile: str = field(default_factory=str)
    scriptfile: str = field(default_factory=str)
    logfile: str = field(default_factory=str)
    logger: logging.Logger = field(default_factory=logging.getLogger)
    filelist: str = field(default_factory=str)
    tclfile_custom_header: Optional[str] = field(default_factory=Optional[str])
    tclfile_custom_body: Optional[str] = field(default_factory=Optional[str])

    @abstractmethod
    def tcl_preamble(self) -> str:
        """Returns a preamble string for the tcl file."""
        pass

    @abstractmethod
    def default_tcl_header(self) -> str:
        """Returns a default header for the tcl file."""
        pass

    def custom_tcl_header(self) -> str:
        """Returns a custom header for the tcl file."""
        if self.tclfile_custom_header:
            with open(self.tclfile_custom_header, "r") as file:
                return "\n".join(file.readlines())

    def tcl_header(self) -> str:
        """Returns a header for the tcl file."""
        if self.tclfile_custom_header:
            return self.custom_tcl_header()
        else:
            return self.default_tcl_header()

    @abstractmethod
    def tcl_analysis_elaborate(self) -> str:
        """Returns a tcl string for the analyze and elaborate steps."""
        pass

    @abstractmethod
    def default_tcl_body(self) -> str:
        """Returns a default body for the tcl file."""
        pass

    def custom_tcl_body(self) -> str:
        """Returns a custom body for the tcl file."""
        if self.tclfile_custom_body:
            with open(self.tclfile_custom_body, "r") as file:
                return "\n".join(file.readlines())

    def tcl_body(self) -> str:
        """Returns a body for the tcl file."""
        if self.tclfile_custom_body:
            return self.custom_tcl_body()
        else:
            return self.default_tcl_body()

    @abstractmethod
    def tcl_footer(self) -> str:
        """Returns a footer for the tcl file."""
        pass

    def tcl(self) -> str:
        """Returns a tcl to be run by an EDA tool."""
        self.logger.info("Generating tcl script.")
        return "\n".join(
            [
                "### Preamble ###",
                self.tcl_preamble(),
                "### Header ###",
                self.tcl_header(),
                "### Analysis & Elaborate ###",
                self.tcl_analysis_elaborate(),
                "### Body ###",
                self.tcl_body(),
                "### Footer ###",
                self.tcl_footer(),
            ]
        )

    @abstractmethod
    def cmd(self) -> str:
        """Returns a shell command to invoke an EDA tool."""
        pass

    def prepare_files(self) -> None:
        """Writes files that are needed before invoking the shell command."""
        write_and_dump_file(
            content=to_filelist(self.srcs),
            filename=self.filelist,
            logger=self.logger,
        )
        if self.tclfile_custom_header:
            dump_file(filename=self.tclfile_custom_header, logger=self.logger)
        if self.tclfile_custom_body:
            dump_file(filename=self.tclfile_custom_body, logger=self.logger)
        write_and_dump_file(
            content=self.tcl(),
            filename=self.tclfile,
            logger=self.logger,
        )
        write_and_dump_file(
            content=self.cmd(),
            filename=self.scriptfile,
            logger=self.logger,
        )

    @abstractmethod
    def run_cmd(self) -> Dict[str, bool]:
        """Prepares files and runs the shell command; returns a dict of success criteria."""
        pass

    @abstractmethod
    def run_test(self) -> bool:
        """Runs the test, summarizes results and returns True if the test was successful."""
        pass
