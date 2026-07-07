#!/bin/bash

cat ${BAZEL_TEST_LOGS_PATH} | grep -E ' in [0-9]+' > ./.bazel-test-outputs.results

python3 ./generate_testplan.py ./.bazel-test-outputs.results ${TEST_CATEGORY}

if [ $? -ne 0 ]; then
  echo "generate_testplan.py failed"
  exit -1
fi

python3 ./generate_testreport.py ./.bazel-test-outputs.results ${BAZEL_TEST_TIMESTAMP} ${TESTLOGS_PATH} ${TEST_CATEGORY}

if [ $? -ne 0 ]; then
  echo "generate_testreport.py failed"
  exit -1
fi
