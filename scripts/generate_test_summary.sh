#!/bin/bash

cat ${BAZEL_TEST_LOGS_PATH} | grep ' in ' > ./.bazel-test-outputs.results

python3 ./generate_testplan.py ./.bazel-test-outputs.results

if [ $? -ne 0 ]; then
  echo "generate_testplan.py failed"
  exit -1
fi

python3 ./generate_testreport.py ./.bazel-test-outputs.results ${BAZEL_TEST_TIMESTAMP_PATH}

if [ $? -ne 0 ]; then
  echo "generate_testreport.py failed"
  exit -1
fi

testplanner ./testplans/*.hjson -s ./testreports/*.hjson -ot ../out/generated/testplan.md \
        -os ../out/sim-res --output-summary-title "Bedrock-RTL tests" --output-summary ../out/sim-res/index.html \
        --project-root ../ --source-url-prefix ${BEDROCK_RTL_SOURCE_URL_PREFIX}
