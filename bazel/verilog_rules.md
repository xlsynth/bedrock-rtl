<!-- Generated with Stardoc: http://skydoc.bazel.build -->

Verilog rules for Bazel.

<a id="rule_verilog_elab_test"></a>

## rule_verilog_elab_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_elab_test")

rule_verilog_elab_test(<a href="#rule_verilog_elab_test-name">name</a>, <a href="#rule_verilog_elab_test-deps">deps</a>, <a href="#rule_verilog_elab_test-defines">defines</a>, <a href="#rule_verilog_elab_test-params">params</a>, <a href="#rule_verilog_elab_test-top">top</a>)
</pre>

Tests that a Verilog or SystemVerilog design elaborates.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_elab_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_elab_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_elab_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_elab_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_elab_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |


<a id="rule_verilog_fpv_test"></a>

## rule_verilog_fpv_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_fpv_test")

rule_verilog_fpv_test(<a href="#rule_verilog_fpv_test-name">name</a>, <a href="#rule_verilog_fpv_test-deps">deps</a>, <a href="#rule_verilog_fpv_test-defines">defines</a>, <a href="#rule_verilog_fpv_test-elab_only">elab_only</a>, <a href="#rule_verilog_fpv_test-opts">opts</a>, <a href="#rule_verilog_fpv_test-params">params</a>, <a href="#rule_verilog_fpv_test-tool">tool</a>, <a href="#rule_verilog_fpv_test-top">top</a>)
</pre>

Runs Verilog/SystemVerilog compilation and formal verification in one command. This rule should be used for simple formal unit tests.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_fpv_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_fpv_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-elab_only"></a>elab_only |  Only run elaboration.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_test-opts"></a>opts |  Tool-specific options not covered by other arguments.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_fpv_test-tool"></a>tool |  Formal tool to use.   | String | required |  |
| <a id="rule_verilog_fpv_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |


<a id="rule_verilog_lint_test"></a>

## rule_verilog_lint_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_lint_test")

rule_verilog_lint_test(<a href="#rule_verilog_lint_test-name">name</a>, <a href="#rule_verilog_lint_test-deps">deps</a>, <a href="#rule_verilog_lint_test-defines">defines</a>, <a href="#rule_verilog_lint_test-params">params</a>, <a href="#rule_verilog_lint_test-top">top</a>)
</pre>

Tests that a Verilog or SystemVerilog design passes a set of static lint checks.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_lint_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_lint_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_lint_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_lint_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_lint_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |


<a id="rule_verilog_sim_test"></a>

## rule_verilog_sim_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_sim_test")

rule_verilog_sim_test(<a href="#rule_verilog_sim_test-name">name</a>, <a href="#rule_verilog_sim_test-deps">deps</a>, <a href="#rule_verilog_sim_test-defines">defines</a>, <a href="#rule_verilog_sim_test-elab_only">elab_only</a>, <a href="#rule_verilog_sim_test-opts">opts</a>, <a href="#rule_verilog_sim_test-params">params</a>, <a href="#rule_verilog_sim_test-seed">seed</a>, <a href="#rule_verilog_sim_test-tool">tool</a>, <a href="#rule_verilog_sim_test-top">top</a>, <a href="#rule_verilog_sim_test-uvm">uvm</a>, <a href="#rule_verilog_sim_test-waves">waves</a>)
</pre>

Runs Verilog/SystemVerilog compilation and simulation in one command. This rule should be used for simple unit tests that do not require multi-step compilation, elaboration, and simulation.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_sim_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_sim_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_sim_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_test-elab_only"></a>elab_only |  Only run elaboration.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_sim_test-opts"></a>opts |  Tool-specific options not covered by other arguments.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_sim_test-seed"></a>seed |  Random seed to use in simulation.   | Integer | optional |  `0`  |
| <a id="rule_verilog_sim_test-tool"></a>tool |  Simulator tool to use.   | String | required |  |
| <a id="rule_verilog_sim_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_sim_test-uvm"></a>uvm |  Run UVM test.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_sim_test-waves"></a>waves |  Enable waveform dumping.   | Boolean | optional |  `False`  |


<a id="get_transitive"></a>

## get_transitive

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "get_transitive")

get_transitive(<a href="#get_transitive-ctx">ctx</a>, <a href="#get_transitive-srcs_not_hdrs">srcs_not_hdrs</a>)
</pre>

Returns a depset of all Verilog source or header files in the transitive closure of the deps attribute.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="get_transitive-ctx"></a>ctx |  <p align="center"> - </p>   |  none |
| <a id="get_transitive-srcs_not_hdrs"></a>srcs_not_hdrs |  <p align="center"> - </p>   |  none |


<a id="verilog_elab_and_lint_test_suite"></a>

## verilog_elab_and_lint_test_suite

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_elab_and_lint_test_suite")

verilog_elab_and_lint_test_suite(<a href="#verilog_elab_and_lint_test_suite-name">name</a>, <a href="#verilog_elab_and_lint_test_suite-defines">defines</a>, <a href="#verilog_elab_and_lint_test_suite-params">params</a>, <a href="#verilog_elab_and_lint_test_suite-kwargs">kwargs</a>)
</pre>

Creates a suite of Verilog elaboration and lint tests for each combination of the provided parameters.

The function generates all possible combinations of the provided parameters and creates a verilog_elab_test
and a verilog_lint_test for each combination. The test names are generated by appending "_elab_test" and "_lint_test"
to the base name followed by the parameter key-values.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_elab_and_lint_test_suite-name"></a>name |  The base name for the test suite.   |  none |
| <a id="verilog_elab_and_lint_test_suite-defines"></a>defines |  A list of defines.   |  `[]` |
| <a id="verilog_elab_and_lint_test_suite-params"></a>params |  A dictionary where keys are parameter names and values are lists of possible values for those parameters.   |  `{}` |
| <a id="verilog_elab_and_lint_test_suite-kwargs"></a>kwargs |  Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.   |  none |


<a id="verilog_elab_test"></a>

## verilog_elab_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_elab_test")

verilog_elab_test(<a href="#verilog_elab_test-tags">tags</a>, <a href="#verilog_elab_test-kwargs">kwargs</a>)
</pre>

Wraps rule_verilog_elab_test with a resource tag: 'resources:verilog_elab_test_tool_licenses:1.'

Useful for having Bazel self-throttle test actions that require a finite number of elab tool licenses.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_elab_test-tags"></a>tags |  <p align="center"> - </p>   |  `[]` |
| <a id="verilog_elab_test-kwargs"></a>kwargs |  <p align="center"> - </p>   |  none |


<a id="verilog_fpv_test"></a>

## verilog_fpv_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_fpv_test")

verilog_fpv_test(<a href="#verilog_fpv_test-tags">tags</a>, <a href="#verilog_fpv_test-kwargs">kwargs</a>)
</pre>

Wraps rule_verilog_fpv_test with a resource tag: 'resources:verilog_fpv_test_tool_licenses:1.'

Useful for having Bazel self-throttle test actions that require a finite number of formal tool licenses.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_fpv_test-tags"></a>tags |  <p align="center"> - </p>   |  `[]` |
| <a id="verilog_fpv_test-kwargs"></a>kwargs |  <p align="center"> - </p>   |  none |


<a id="verilog_fpv_test_suite"></a>

## verilog_fpv_test_suite

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_fpv_test_suite")

verilog_fpv_test_suite(<a href="#verilog_fpv_test_suite-name">name</a>, <a href="#verilog_fpv_test_suite-defines">defines</a>, <a href="#verilog_fpv_test_suite-params">params</a>, <a href="#verilog_fpv_test_suite-kwargs">kwargs</a>)
</pre>

Creates a suite of Verilog fpv tests for each combination of the provided parameters.

The function generates all possible combinations of the provided parameters and creates a verilog_fpv_test
for each combination. The test names are generated by appending "_fpv_test"
to the base name followed by the parameter key-values.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_fpv_test_suite-name"></a>name |  The base name for the test suite.   |  none |
| <a id="verilog_fpv_test_suite-defines"></a>defines |  A list of defines.   |  `[]` |
| <a id="verilog_fpv_test_suite-params"></a>params |  A dictionary where keys are parameter names and values are lists of possible values for those parameters.   |  `{}` |
| <a id="verilog_fpv_test_suite-kwargs"></a>kwargs |  Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.   |  none |


<a id="verilog_lint_test"></a>

## verilog_lint_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_lint_test")

verilog_lint_test(<a href="#verilog_lint_test-tags">tags</a>, <a href="#verilog_lint_test-kwargs">kwargs</a>)
</pre>

Wraps rule_verilog_lint_test with a resource tag: 'resources:verilog_lint_test_tool_licenses:1.'

Useful for having Bazel self-throttle test actions that require a finite number of lint tool licenses.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_lint_test-tags"></a>tags |  <p align="center"> - </p>   |  `[]` |
| <a id="verilog_lint_test-kwargs"></a>kwargs |  <p align="center"> - </p>   |  none |


<a id="verilog_sim_test"></a>

## verilog_sim_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_sim_test")

verilog_sim_test(<a href="#verilog_sim_test-tags">tags</a>, <a href="#verilog_sim_test-kwargs">kwargs</a>)
</pre>

Wraps rule_verilog_sim_test with a resource tag: 'resources:verilog_sim_test_tool_licenses:1.'

Useful for having Bazel self-throttle test actions that require a finite number of simulator tool licenses.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_sim_test-tags"></a>tags |  <p align="center"> - </p>   |  `[]` |
| <a id="verilog_sim_test-kwargs"></a>kwargs |  <p align="center"> - </p>   |  none |
