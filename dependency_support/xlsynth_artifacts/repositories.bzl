# SPDX-License-Identifier: Apache-2.0

"""Repository rules for XLSynth release artifacts.

TopStitch links against the `libxls` DSO through the `xlsynth-sys` crate.
Although `xlsynth-sys` downloads that DSO during its Rust build script, Bazel
does not automatically expose Cargo build-script outputs as runtime inputs for
later actions that execute `//stitch:stitch_tool`. This repository rule makes
the DSO a declared Bazel input so wrapper-generation actions can run hermetically
inside their sandboxes.

The `xlsynth-sys` version is read from `stitch/Cargo.lock`, keeping TopStitch's
Cargo dependency graph as the source of truth. Dependabot can then bump
TopStitch, lockfile regeneration can update `xlsynth-sys`, and this rule will
download the matching XLS release artifact without requiring synchronized
Dockerfile edits.
"""

def _parse_xlsynth_sys_version(cargo_lock):
    current_name = None
    current_version = None

    for line in cargo_lock.splitlines():
        line = line.strip()
        if line == "[[package]]":
            if current_name == "xlsynth-sys" and current_version:
                return current_version
            current_name = None
            current_version = None
            continue

        if line.startswith("name = "):
            current_name = line.split("\"")[1]
        elif current_name and line.startswith("version = "):
            current_version = line.split("\"")[1]

    if current_name == "xlsynth-sys" and current_version:
        return current_version

    fail("Could not find package `xlsynth-sys` in Cargo.lock")

def _xlsynth_artifacts_repository_impl(repository_ctx):
    cargo_lock = repository_ctx.read(repository_ctx.attr.cargo_lock)
    version = _parse_xlsynth_sys_version(cargo_lock)
    tag = "v%s" % version

    dso_filename = "libxls-%s-%s.so" % (tag, repository_ctx.attr.lib_suffix)
    dso_gz_filename = "%s.gz" % dso_filename
    release_url = "https://github.com/xlsynth/xlsynth/releases/download/%s/libxls-%s.so.gz" % (
        tag,
        repository_ctx.attr.lib_suffix,
    )

    checksum_file = "libxls.sha256"
    repository_ctx.download(
        url = "%s.sha256" % release_url,
        output = checksum_file,
    )
    checksum = repository_ctx.read(checksum_file).strip().split(" ")[0]

    repository_ctx.download(
        url = release_url,
        output = dso_gz_filename,
        sha256 = checksum,
    )
    result = repository_ctx.execute(["gzip", "-df", dso_gz_filename])
    if result.return_code != 0:
        fail("Failed to decompress %s:\n%s" % (dso_gz_filename, result.stderr))

    repository_ctx.file(
        "BUILD.bazel",
        """# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "xls_dso",
    srcs = ["{dso_filename}"],
)
""".format(dso_filename = dso_filename),
    )

xlsynth_artifacts_repository = repository_rule(
    implementation = _xlsynth_artifacts_repository_impl,
    attrs = {
        "cargo_lock": attr.label(
            allow_single_file = True,
            mandatory = True,
        ),
        "lib_suffix": attr.string(
            default = "rocky8",
            values = [
                "rocky8",
                "ubuntu2004",
            ],
        ),
    },
)
