# Copyright 2020 The XLS Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


#################################################################################
# Stripped-down version of https://github.com/google/xls/blob/main/dependency_support/initialize_external.bzl,
# taking only what is needed to get @rules_hdl working. Retains the XLS copyright notice.
#################################################################################


"""Provides helper that initializes external repositories with third-party code."""

load("@project_python//:defs.bzl", python_interpreter_target = "interpreter")
load("@rules_hdl//:init.bzl", rules_hdl_init = "init")
load("@rules_hdl//dependency_support:dependency_support.bzl", rules_hdl_dependency_support = "dependency_support")

def initialize_external_repositories():
    """Calls set-up methods for external repositories that require that."""
    rules_hdl_init(python_interpreter_target = python_interpreter_target)
    rules_hdl_dependency_support()