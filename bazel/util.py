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

from typing import List

def check_each_filename_suffix(filenames: List[str], suffices: List[str]) -> None:
    """Raises ValueError if there is any filename in the list that doesn't end with any of the expected suffices."""
    for filename in filenames:
        match = False
        for suffix in suffices:
            if filename.endswith(suffix):
                match = True
                break
        if not match:
            raise ValueError(f"Expected filename to end with any of {suffices}: {filename}")
