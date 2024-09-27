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
# Stripped-down version of https://github.com/google/xls/blob/main/dependency_support/load_external.bzl,
# taking only what is needed to get @rules_hdl working. Retains the XLS copyright notice.
#################################################################################

"""Provides helper that loads external repositories with third-party code."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("//dependency_support/boost:workspace.bzl", repo_boost = "repo")
load("//dependency_support/rules_hdl:workspace.bzl", repo_rules_hdl = "repo")

def load_external_repositories():
    """Loads external repositories with third-party code."""

    # Note: there are more direct dependencies than are explicitly listed here.
    #
    # By letting direct dependencies be satisfied by transitive WORKSPACE
    # setups we let the transitive dependency versions "float" to satisfy their
    # package requirements, so that we can bump our dependency versions here
    # more easily without debugging/resolving unnecessary conflicts.
    #
    # This situation will change when Bedrock-RTL moves to bzlmod. See
    # https://github.com/google/xls/issues/865 and
    # https://github.com/google/xls/issues/931#issue-1667228764 for more
    # information / background.

    repo_boost()
    repo_rules_hdl()

    # Released on 2022-12-27.
    # Current as of 2024-06-26 would be 6.0.2, but that does not work yet
    # with rules_hdl (it assumes rules_proto_toolchains is in repositories.bzl)
    # https://github.com/bazelbuild/rules_proto/releases/tag/5.3.0-21.7
    http_archive(
        name = "rules_proto",
        sha256 = "dc3fb206a2cb3441b485eb1e423165b231235a1ea9b031b4433cf7bc1fa460dd",
        strip_prefix = "rules_proto-5.3.0-21.7",
        urls = [
            "https://github.com/bazelbuild/rules_proto/archive/refs/tags/5.3.0-21.7.tar.gz",
        ],
    )

    # Released on 2024-06-19, current as of 2024-06-26
    http_archive(
        name = "rules_python",
        sha256 = "e3f1cc7a04d9b09635afb3130731ed82b5f58eadc8233d4efb59944d92ffc06f",
        strip_prefix = "rules_python-0.33.2",
        url = "https://github.com/bazelbuild/rules_python/releases/download/0.33.2/rules_python-0.33.2.tar.gz",
    )

    # Released 2024-06-07, current as of 2024-06-26.
    http_archive(
        name = "com_github_grpc_grpc",
        urls = ["https://github.com/grpc/grpc/archive/v1.64.2.tar.gz"],
        patches = ["//dependency_support/com_github_grpc_grpc:0001-Add-absl-status-to-deps.patch"],
        sha256 = "c682fc39baefc6e804d735e6b48141157b7213602cc66dbe0bf375b904d8b5f9",
        strip_prefix = "grpc-1.64.2",
        repo_mapping = {
            "@local_config_python": "@project_python",
            "@system_python": "@project_python",
        },
    )
