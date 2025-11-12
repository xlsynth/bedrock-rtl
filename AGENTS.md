# Instructions for AI Agents

First, read the `README.adoc` file completely before proceeding.
We use the Bazel build system.

To build targets, just run this:

```shell
bazel build //...
```

But to run most tests, you need a properly configured environment with access to relevant EDA tools, some of which are proprietary, as mentioned in the README.
To check if this is configured properly, read through `.bazelrc` and also check if there is a `user.bazelrc`.
If it looks like any of the required environment variables are not set or they're set to invalid paths, the environment may not be set up correctly.
You can smoke-test if the environment looks ready:

```shell
bazel run //:check_env
```

Assuming it's ok, you can run all tests:

```shell
bazel test //...
```

The above might take a long time, especially because proprietary EDA tools are typically license-limited and that can limit Bazel's test-level concurrency.
You can filter to run fewer tests using the typical Bazel path syntax.
We've also provided handy test tag filters by test type and by vendor tool.
For example:

```shell
bazel test //... --test_tag-filters=elab  # Run only elaboration tests
bazel test //... --test_tag-filters=verific  # Run only tests that use the `verific` tool
bazel test //... --test_tag-filters=sim  # Run only simulation tests, with all applicable tools
bazel test //... --test_tag-filters=dsim  # Run only tests that use the `dsim` tool (subset of all simulation tests)
```

Note that some Bazel tests do not require any EDA tools.
Notably:

```shell
bazel test //bazel/... //python/...
```

`pre-commit` will run code formatters.
