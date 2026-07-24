# Report generation scripts


In `scripts/` there are 3 scripts used to generate a static web page with test results.

### generate_testplan.py


Python script that takes in a file containing a list of passed/failed tests printed by Bazel and the name of the test category.
The file containing a list of tests shall be in the following format:

**Bazel logs**

```
//amba/sim:br_amba_axi_demux_tb_sim_test_tools_suite_verilator_sim_test PASSED in 16.5s
//<test_path>:<test_name> <result> in <time>
```

For each test path, it generates `.hjson` files in `testplans/` which are later used by
[testplanner](https://github.com/antmicro/testplanner) to generate a web page.

### generate_testreport.py


Python script that takes in a file containing a list of passed/failed tests printed by Bazel in the same format as
`generate_testplan.py`, path to file containing the timestamp when Bazel started running the tests, path to directory
containing test logs and the name of the test category.
For each test path, it generates `hjson` files in `testreports/` which are later used by
[testplanner](https://github.com/antmicro/testplanner) to generate a web page.

### generate_test_summary.sh


Bash script that executes the report generation scripts described above to generate every file needed
by `testplanner` to generate a report web page. A few environment variables have to be set for it to work properly:

- BAZEL_TEST_LOGS_PATH - path to file containing output from a `bazel test` run, used to generate a list of failing/passing tests.
- BAZEL_TEST_TIMESTAMP - timestamp of when Bazel tests were ran.
- BEDROCK_RTL_SOURCE_URL_PREFIX - URL base of the `bedrock-rtl` repository.
- TESTLOGS_PATH - path to directory containing logs from Bazel (Bazel leaves it in the bazel-testlogs directory).
- TEST_SUMMARY_OUTPUT_DIR - path to directory where the static web page will be deployed.
- BEDROCK_RTL_PROJECT_ROOT - path to the root of `bedrock-rtl` repository.
- TEST_CATEGORY - category of tests being ran, f.e. `verilator` `slang`.
