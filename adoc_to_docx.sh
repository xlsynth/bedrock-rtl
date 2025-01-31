#!/bin/bash

# Copyright 2024-2025 The Bedrock-RTL Authors
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

# Converts a single .adoc file to .docx format.
# Helpful for working with ChipStack.
#
# Usage: ./adoc_to_docx.sh <input-file.adoc>
# Example: ./adoc_to_docx.sh example.adoc
# This will produce example.docbook and example.docx as outputs.

if [ $# -lt 1 ]; then
    echo "Error: No input file provided."
    exit 1
fi

if [[ ! $1 == *.adoc ]]; then
    echo "Error: Input file must have a .adoc extension."
    exit 1
fi

set -e

ADOC=$1
DOCBOOK="${ADOC%.adoc}.docbook"
DOCX="${DOCBOOK%.docbook}.docx"

asciidoctor -b docbook $ADOC -o $DOCBOOK
pandoc -f docbook $DOCBOOK -o $DOCX
