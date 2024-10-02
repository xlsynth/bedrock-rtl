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

from typing import List, Optional

def verilog_elab_test_impl(hdrs: Optional[List[str]], srcs: List[str], top: str) -> bool:
    """Returns True if the top-level Verilog or SystemVerilog module is able to elaborate; may print to stdout and/or stderr."""
    # TODO: Implement this using your own tool.
    return True
