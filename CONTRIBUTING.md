<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contributing to Bedrock-RTL

Thank you for contributing. For local setup, testing, and development tools, see
[DEVELOPING.md](DEVELOPING.md).

## Pull-request requirements

Before a pull request can merge, it needs:

- One approval badge from a maintainer.
- All CI checks to pass.

## Continuous integration

GitHub Actions divides CI into public OSS-based checks and private proprietary-tool
checks.

### Public OSS-based checks

GitHub-hosted runners run pre-commit, build the public Docker image, and run the
public test suites. The Bazel tests are sharded across Python/ecc code generation,
Stardoc, Slang elaboration, and Verilator simulation. The
`bazel-oss-tool-test` check combines the shard results.

### Proprietary-tool checks

A self-hosted GitHub Actions runner runs the proprietary-tool lane. It builds the
repository and runs Verific elaboration, RealIntent AscentLint, and Synopsys VCS
tests. JasperGold formal tests run in the nightly workflow.

The self-hosted runner's detailed logs are not shown in GitHub Actions. This keeps
third-party vendor IP out of public logs while still reporting the overall check
result.

If you need help debugging a proprietary test failure, contact a maintainer
listed in [MAINTAINERS.md](MAINTAINERS.md).
