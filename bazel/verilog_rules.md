<!-- Generated with Stardoc: http://skydoc.bazel.build -->

Verilog rules for Bazel.

<a id="generate_instantiation_wrapper"></a>

## generate_instantiation_wrapper

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "generate_instantiation_wrapper")

generate_instantiation_wrapper(<a href="#generate_instantiation_wrapper-name">name</a>, <a href="#generate_instantiation_wrapper-deps">deps</a>, <a href="#generate_instantiation_wrapper-disable_lint_rules">disable_lint_rules</a>, <a href="#generate_instantiation_wrapper-param_file">param_file</a>, <a href="#generate_instantiation_wrapper-stitch_tool">stitch_tool</a>, <a href="#generate_instantiation_wrapper-top">top</a>,
                               <a href="#generate_instantiation_wrapper-wrapper_name">wrapper_name</a>)
</pre>



**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="generate_instantiation_wrapper-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="generate_instantiation_wrapper-deps"></a>deps |  -   | <a href="https://bazel.build/concepts/labels">List of labels</a> | required |  |
| <a id="generate_instantiation_wrapper-disable_lint_rules"></a>disable_lint_rules |  -   | List of strings | optional |  `[]`  |
| <a id="generate_instantiation_wrapper-param_file"></a>param_file |  -   | <a href="https://bazel.build/concepts/labels">Label</a> | required |  |
| <a id="generate_instantiation_wrapper-stitch_tool"></a>stitch_tool |  -   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//stitch:stitch_tool"`  |
| <a id="generate_instantiation_wrapper-top"></a>top |  -   | String | required |  |
| <a id="generate_instantiation_wrapper-wrapper_name"></a>wrapper_name |  -   | String | required |  |


<a id="generate_parameter_file"></a>

## generate_parameter_file

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "generate_parameter_file")

generate_parameter_file(<a href="#generate_parameter_file-name">name</a>, <a href="#generate_parameter_file-params">params</a>)
</pre>



**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="generate_parameter_file-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="generate_parameter_file-params"></a>params |  -   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> List of strings</a> | required |  |


<a id="rule_verilog_elab_test"></a>

## rule_verilog_elab_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_elab_test")

rule_verilog_elab_test(<a href="#rule_verilog_elab_test-name">name</a>, <a href="#rule_verilog_elab_test-deps">deps</a>, <a href="#rule_verilog_elab_test-compile_only">compile_only</a>, <a href="#rule_verilog_elab_test-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_elab_test-custom_tcl_header">custom_tcl_header</a>, <a href="#rule_verilog_elab_test-defines">defines</a>, <a href="#rule_verilog_elab_test-opts">opts</a>,
                       <a href="#rule_verilog_elab_test-params">params</a>, <a href="#rule_verilog_elab_test-runner_flags">runner_flags</a>, <a href="#rule_verilog_elab_test-tool">tool</a>, <a href="#rule_verilog_elab_test-top">top</a>, <a href="#rule_verilog_elab_test-verilog_runner_data">verilog_runner_data</a>, <a href="#rule_verilog_elab_test-verilog_runner_env">verilog_runner_env</a>,
                       <a href="#rule_verilog_elab_test-verilog_runner_plugins">verilog_runner_plugins</a>, <a href="#rule_verilog_elab_test-verilog_runner_tool">verilog_runner_tool</a>)
</pre>

Tests that a Verilog or SystemVerilog design elaborates. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_elab_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_elab_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_elab_test-compile_only"></a>compile_only |  Compile and type-check sources without elaborating a top-level module.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_elab_test-custom_tcl_body"></a>custom_tcl_body |  Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step.The tcl body (custom or not) is unconditionally followed by the tcl footer.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_elab_test-custom_tcl_header"></a>custom_tcl_header |  Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script.The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_elab_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_elab_test-opts"></a>opts |  Tool-specific elaboration options.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_elab_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_elab_test-runner_flags"></a>runner_flags |  command line flags   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_elab_test-tool"></a>tool |  Elaboration tool to use.   | String | required |  |
| <a id="rule_verilog_elab_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_elab_test-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_elab_test-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_elab_test-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:slang.py", "@bedrock-rtl//python/verilog_runner/plugins:verilator.py"]`  |
| <a id="rule_verilog_elab_test-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |


<a id="rule_verilog_fpv_sandbox"></a>

## rule_verilog_fpv_sandbox

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_fpv_sandbox")

rule_verilog_fpv_sandbox(<a href="#rule_verilog_fpv_sandbox-name">name</a>, <a href="#rule_verilog_fpv_sandbox-deps">deps</a>, <a href="#rule_verilog_fpv_sandbox-data">data</a>, <a href="#rule_verilog_fpv_sandbox-analysis_opts">analysis_opts</a>, <a href="#rule_verilog_fpv_sandbox-conn">conn</a>, <a href="#rule_verilog_fpv_sandbox-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_fpv_sandbox-custom_tcl_header">custom_tcl_header</a>,
                         <a href="#rule_verilog_fpv_sandbox-defines">defines</a>, <a href="#rule_verilog_fpv_sandbox-elab_only">elab_only</a>, <a href="#rule_verilog_fpv_sandbox-elab_opts">elab_opts</a>, <a href="#rule_verilog_fpv_sandbox-gui">gui</a>, <a href="#rule_verilog_fpv_sandbox-opts">opts</a>, <a href="#rule_verilog_fpv_sandbox-params">params</a>, <a href="#rule_verilog_fpv_sandbox-runner_flags">runner_flags</a>, <a href="#rule_verilog_fpv_sandbox-tool">tool</a>, <a href="#rule_verilog_fpv_sandbox-top">top</a>,
                         <a href="#rule_verilog_fpv_sandbox-verilog_runner_data">verilog_runner_data</a>, <a href="#rule_verilog_fpv_sandbox-verilog_runner_env">verilog_runner_env</a>, <a href="#rule_verilog_fpv_sandbox-verilog_runner_plugins">verilog_runner_plugins</a>,
                         <a href="#rule_verilog_fpv_sandbox-verilog_runner_tool">verilog_runner_tool</a>)
</pre>

Writes FPV files and run scripts into a tarball for independent execution outside of Bazel.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_fpv_sandbox-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_fpv_sandbox-deps"></a>deps |  The Verilog dependencies of the sandbox.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_fpv_sandbox-data"></a>data |  Additional files to copy into the sandbox tarball.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_fpv_sandbox-analysis_opts"></a>analysis_opts |  custom analysis options   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_sandbox-conn"></a>conn |  Switch to connectivity   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_sandbox-custom_tcl_body"></a>custom_tcl_body |  Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step.The tcl body (custom or not) is unconditionally followed by the tcl footer.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_fpv_sandbox-custom_tcl_header"></a>custom_tcl_header |  Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script.The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_fpv_sandbox-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_sandbox-elab_only"></a>elab_only |  Only run elaboration.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_sandbox-elab_opts"></a>elab_opts |  custom elab options   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_sandbox-gui"></a>gui |  Enable GUI.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_sandbox-opts"></a>opts |  Tool-specific options not covered by other arguments.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_sandbox-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_fpv_sandbox-runner_flags"></a>runner_flags |  jg flags   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_fpv_sandbox-tool"></a>tool |  Formal tool to use.   | String | required |  |
| <a id="rule_verilog_fpv_sandbox-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_fpv_sandbox-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_fpv_sandbox-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_fpv_sandbox-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:verilator.py"]`  |
| <a id="rule_verilog_fpv_sandbox-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |


<a id="rule_verilog_fpv_test"></a>

## rule_verilog_fpv_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_fpv_test")

rule_verilog_fpv_test(<a href="#rule_verilog_fpv_test-name">name</a>, <a href="#rule_verilog_fpv_test-deps">deps</a>, <a href="#rule_verilog_fpv_test-data">data</a>, <a href="#rule_verilog_fpv_test-analysis_opts">analysis_opts</a>, <a href="#rule_verilog_fpv_test-conn">conn</a>, <a href="#rule_verilog_fpv_test-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_fpv_test-custom_tcl_header">custom_tcl_header</a>,
                      <a href="#rule_verilog_fpv_test-defines">defines</a>, <a href="#rule_verilog_fpv_test-elab_only">elab_only</a>, <a href="#rule_verilog_fpv_test-elab_opts">elab_opts</a>, <a href="#rule_verilog_fpv_test-gui">gui</a>, <a href="#rule_verilog_fpv_test-opts">opts</a>, <a href="#rule_verilog_fpv_test-params">params</a>, <a href="#rule_verilog_fpv_test-runner_flags">runner_flags</a>, <a href="#rule_verilog_fpv_test-tool">tool</a>, <a href="#rule_verilog_fpv_test-top">top</a>,
                      <a href="#rule_verilog_fpv_test-verilog_runner_data">verilog_runner_data</a>, <a href="#rule_verilog_fpv_test-verilog_runner_env">verilog_runner_env</a>, <a href="#rule_verilog_fpv_test-verilog_runner_plugins">verilog_runner_plugins</a>,
                      <a href="#rule_verilog_fpv_test-verilog_runner_tool">verilog_runner_tool</a>)
</pre>

Runs Verilog/SystemVerilog compilation and formal verification in one command. This rule should be used for simple formal unit tests. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_fpv_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_fpv_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-data"></a>data |  Additional files to copy into the runfiles tree for the FPV job.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-analysis_opts"></a>analysis_opts |  custom analysis options   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-conn"></a>conn |  Switch to connectivity   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_test-custom_tcl_body"></a>custom_tcl_body |  Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step.The tcl body (custom or not) is unconditionally followed by the tcl footer.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_fpv_test-custom_tcl_header"></a>custom_tcl_header |  Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script.The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_fpv_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-elab_only"></a>elab_only |  Only run elaboration.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_test-elab_opts"></a>elab_opts |  custom elab options   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-gui"></a>gui |  Enable GUI.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_fpv_test-opts"></a>opts |  Tool-specific options not covered by other arguments. If provided, then 'tool' must also be set.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_fpv_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_fpv_test-runner_flags"></a>runner_flags |  jg flags   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_fpv_test-tool"></a>tool |  Formal tool to use.   | String | required |  |
| <a id="rule_verilog_fpv_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_fpv_test-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_fpv_test-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_fpv_test-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:verilator.py"]`  |
| <a id="rule_verilog_fpv_test-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |


<a id="rule_verilog_lint_test"></a>

## rule_verilog_lint_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_lint_test")

rule_verilog_lint_test(<a href="#rule_verilog_lint_test-name">name</a>, <a href="#rule_verilog_lint_test-deps">deps</a>, <a href="#rule_verilog_lint_test-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_lint_test-custom_tcl_header">custom_tcl_header</a>, <a href="#rule_verilog_lint_test-defines">defines</a>, <a href="#rule_verilog_lint_test-params">params</a>, <a href="#rule_verilog_lint_test-policy">policy</a>,
                       <a href="#rule_verilog_lint_test-runner_flags">runner_flags</a>, <a href="#rule_verilog_lint_test-tool">tool</a>, <a href="#rule_verilog_lint_test-top">top</a>, <a href="#rule_verilog_lint_test-verilog_runner_data">verilog_runner_data</a>, <a href="#rule_verilog_lint_test-verilog_runner_env">verilog_runner_env</a>,
                       <a href="#rule_verilog_lint_test-verilog_runner_plugins">verilog_runner_plugins</a>, <a href="#rule_verilog_lint_test-verilog_runner_tool">verilog_runner_tool</a>)
</pre>

Tests that a Verilog or SystemVerilog design passes a set of static lint checks. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_lint_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_lint_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_lint_test-custom_tcl_body"></a>custom_tcl_body |  Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step.The tcl body (custom or not) is unconditionally followed by the tcl footer.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_lint_test-custom_tcl_header"></a>custom_tcl_header |  Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script.The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_lint_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_lint_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_lint_test-policy"></a>policy |  The lint policy file to use. If not provided, then the default tool policy is used (typically provided through an environment variable).   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_lint_test-runner_flags"></a>runner_flags |  command line flags   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_lint_test-tool"></a>tool |  Lint tool to use.   | String | required |  |
| <a id="rule_verilog_lint_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_lint_test-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_lint_test-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_lint_test-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:verilator.py"]`  |
| <a id="rule_verilog_lint_test-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |


<a id="rule_verilog_sim_coverage_aggregate"></a>

## rule_verilog_sim_coverage_aggregate

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_sim_coverage_aggregate")

rule_verilog_sim_coverage_aggregate(<a href="#rule_verilog_sim_coverage_aggregate-name">name</a>, <a href="#rule_verilog_sim_coverage_aggregate-deps">deps</a>, <a href="#rule_verilog_sim_coverage_aggregate-all_srcs">all_srcs</a>, <a href="#rule_verilog_sim_coverage_aggregate-coverage_data">coverage_data</a>, <a href="#rule_verilog_sim_coverage_aggregate-coverage_reports">coverage_reports</a>)
</pre>

Merges coverage info files and packs a Coverview ZIP as a declared Bazel output.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_sim_coverage_aggregate-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_sim_coverage_aggregate-deps"></a>deps |  The dependencies of the testbench whose design sources should be included in sources.txt.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_aggregate-all_srcs"></a>all_srcs |  Target defining all sources that should be included in the aggregated coverage.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_coverage_aggregate-coverage_data"></a>coverage_data |  Coverage data targets whose info files should be merged.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_aggregate-coverage_reports"></a>coverage_reports |  Coverage report targets whose transitive info files should be merged.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |


<a id="rule_verilog_sim_coverage_data"></a>

## rule_verilog_sim_coverage_data

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_sim_coverage_data")

rule_verilog_sim_coverage_data(<a href="#rule_verilog_sim_coverage_data-name">name</a>, <a href="#rule_verilog_sim_coverage_data-deps">deps</a>, <a href="#rule_verilog_sim_coverage_data-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_sim_coverage_data-custom_tcl_header">custom_tcl_header</a>, <a href="#rule_verilog_sim_coverage_data-defines">defines</a>, <a href="#rule_verilog_sim_coverage_data-elab_only">elab_only</a>,
                               <a href="#rule_verilog_sim_coverage_data-elab_opts">elab_opts</a>, <a href="#rule_verilog_sim_coverage_data-opts">opts</a>, <a href="#rule_verilog_sim_coverage_data-params">params</a>, <a href="#rule_verilog_sim_coverage_data-runner_flags">runner_flags</a>, <a href="#rule_verilog_sim_coverage_data-seed">seed</a>, <a href="#rule_verilog_sim_coverage_data-sim_opts">sim_opts</a>, <a href="#rule_verilog_sim_coverage_data-tool">tool</a>, <a href="#rule_verilog_sim_coverage_data-top">top</a>, <a href="#rule_verilog_sim_coverage_data-uvm">uvm</a>,
                               <a href="#rule_verilog_sim_coverage_data-verilog_runner_data">verilog_runner_data</a>, <a href="#rule_verilog_sim_coverage_data-verilog_runner_env">verilog_runner_env</a>, <a href="#rule_verilog_sim_coverage_data-verilog_runner_plugins">verilog_runner_plugins</a>,
                               <a href="#rule_verilog_sim_coverage_data-verilog_runner_tool">verilog_runner_tool</a>, <a href="#rule_verilog_sim_coverage_data-waves">waves</a>)
</pre>

Runs a Verilator simulation test target and emits coverage info and description files.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_sim_coverage_data-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_sim_coverage_data-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_data-custom_tcl_body"></a>custom_tcl_body |  Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step.The tcl body (custom or not) is unconditionally followed by the tcl footer.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_coverage_data-custom_tcl_header"></a>custom_tcl_header |  Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script.The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_coverage_data-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_data-elab_only"></a>elab_only |  Only run elaboration.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_sim_coverage_data-elab_opts"></a>elab_opts |  Tool-specific compile/elaboration options not covered by other arguments.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_data-opts"></a>opts |  Deprecated VCS-only simulation options. Prefer 'elab_opts' or 'sim_opts'.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_data-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_sim_coverage_data-runner_flags"></a>runner_flags |  command line flags   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_sim_coverage_data-seed"></a>seed |  Random seed to use in simulation.   | Integer | optional |  `0`  |
| <a id="rule_verilog_sim_coverage_data-sim_opts"></a>sim_opts |  Tool-specific simulation runtime options, such as simulator plusargs.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_coverage_data-tool"></a>tool |  Simulator tool to use.   | String | required |  |
| <a id="rule_verilog_sim_coverage_data-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_sim_coverage_data-uvm"></a>uvm |  Run UVM test.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_sim_coverage_data-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_sim_coverage_data-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_coverage_data-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:verilator.py"]`  |
| <a id="rule_verilog_sim_coverage_data-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |
| <a id="rule_verilog_sim_coverage_data-waves"></a>waves |  Enable waveform dumping.   | Boolean | optional |  `False`  |


<a id="rule_verilog_sim_test"></a>

## rule_verilog_sim_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_sim_test")

rule_verilog_sim_test(<a href="#rule_verilog_sim_test-name">name</a>, <a href="#rule_verilog_sim_test-deps">deps</a>, <a href="#rule_verilog_sim_test-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_sim_test-custom_tcl_header">custom_tcl_header</a>, <a href="#rule_verilog_sim_test-defines">defines</a>, <a href="#rule_verilog_sim_test-elab_only">elab_only</a>, <a href="#rule_verilog_sim_test-elab_opts">elab_opts</a>,
                      <a href="#rule_verilog_sim_test-opts">opts</a>, <a href="#rule_verilog_sim_test-params">params</a>, <a href="#rule_verilog_sim_test-runner_flags">runner_flags</a>, <a href="#rule_verilog_sim_test-seed">seed</a>, <a href="#rule_verilog_sim_test-sim_opts">sim_opts</a>, <a href="#rule_verilog_sim_test-tool">tool</a>, <a href="#rule_verilog_sim_test-top">top</a>, <a href="#rule_verilog_sim_test-uvm">uvm</a>, <a href="#rule_verilog_sim_test-verilog_runner_data">verilog_runner_data</a>,
                      <a href="#rule_verilog_sim_test-verilog_runner_env">verilog_runner_env</a>, <a href="#rule_verilog_sim_test-verilog_runner_plugins">verilog_runner_plugins</a>, <a href="#rule_verilog_sim_test-verilog_runner_tool">verilog_runner_tool</a>, <a href="#rule_verilog_sim_test-waves">waves</a>)
</pre>

Runs Verilog/SystemVerilog compilation and simulation in one command. This rule should be used for simple unit tests that do not require multi-step compilation, elaboration, and simulation. Needs VERILOG_RUNNER_PLUGIN_PATH environment variable to be set correctly.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_sim_test-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_sim_test-deps"></a>deps |  The dependencies of the test.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_sim_test-custom_tcl_body"></a>custom_tcl_body |  Tcl script file containing custom tool-specific commands to insert in the middle of the generated tcl script after the elaboration step.The tcl body (custom or not) is unconditionally followed by the tcl footer.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_test-custom_tcl_header"></a>custom_tcl_header |  Tcl script file containing custom tool-specific commands to insert at the beginning of the generated tcl script.The tcl header (custom or not) is unconditionally followed by analysis and elaborate commands, and then the tcl body.Do not include Tcl commands that manipulate sources, headers, defines, or parameters, as those will be handled by the rule implementation.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_test-defines"></a>defines |  Preprocessor defines to pass to the Verilog compiler.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_test-elab_only"></a>elab_only |  Only run elaboration.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_sim_test-elab_opts"></a>elab_opts |  Tool-specific compile/elaboration options not covered by other arguments.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_test-opts"></a>opts |  Deprecated VCS-only simulation options. Prefer 'elab_opts' or 'sim_opts'.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_test-params"></a>params |  Verilog module parameters to set in the instantiation of the top-level module.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_sim_test-runner_flags"></a>runner_flags |  command line flags   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_sim_test-seed"></a>seed |  Random seed to use in simulation.   | Integer | optional |  `0`  |
| <a id="rule_verilog_sim_test-sim_opts"></a>sim_opts |  Tool-specific simulation runtime options, such as simulator plusargs.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_sim_test-tool"></a>tool |  Simulator tool to use.   | String | required |  |
| <a id="rule_verilog_sim_test-top"></a>top |  The top-level module; if not provided and there exists one dependency, then defaults to that dep's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_sim_test-uvm"></a>uvm |  Run UVM test.   | Boolean | optional |  `False`  |
| <a id="rule_verilog_sim_test-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_sim_test-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_sim_test-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog runner plugins to load from this workspace, in addition to those loaded from VERILOG_RUNNER_PLUGIN_PATH.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:verilator.py"]`  |
| <a id="rule_verilog_sim_test-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |
| <a id="rule_verilog_sim_test-waves"></a>waves |  Enable waveform dumping.   | Boolean | optional |  `False`  |


<a id="rule_verilog_synth"></a>

## rule_verilog_synth

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_synth")

rule_verilog_synth(<a href="#rule_verilog_synth-name">name</a>, <a href="#rule_verilog_synth-deps">deps</a>, <a href="#rule_verilog_synth-data">data</a>, <a href="#rule_verilog_synth-clock_period_ps">clock_period_ps</a>, <a href="#rule_verilog_synth-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_synth-custom_tcl_header">custom_tcl_header</a>, <a href="#rule_verilog_synth-defines">defines</a>,
                   <a href="#rule_verilog_synth-liberty">liberty</a>, <a href="#rule_verilog_synth-opts">opts</a>, <a href="#rule_verilog_synth-params">params</a>, <a href="#rule_verilog_synth-runner_flags">runner_flags</a>, <a href="#rule_verilog_synth-tool">tool</a>, <a href="#rule_verilog_synth-top">top</a>, <a href="#rule_verilog_synth-verilog_runner_data">verilog_runner_data</a>,
                   <a href="#rule_verilog_synth-verilog_runner_env">verilog_runner_env</a>, <a href="#rule_verilog_synth-verilog_runner_plugins">verilog_runner_plugins</a>, <a href="#rule_verilog_synth-verilog_runner_tool">verilog_runner_tool</a>)
</pre>

Runs logic synthesis for a Verilog or SystemVerilog design and prints the tool report. This is an executable target, not a test.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_synth-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_synth-deps"></a>deps |  Verilog libraries containing the design to synthesize.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_synth-data"></a>data |  Additional runtime files needed by the synthesis plugin.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_synth-clock_period_ps"></a>clock_period_ps |  Optional target clock period in picoseconds; requires liberty.   | Integer | optional |  `0`  |
| <a id="rule_verilog_synth-custom_tcl_body"></a>custom_tcl_body |  Optional tool-specific Tcl body.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth-custom_tcl_header"></a>custom_tcl_header |  Optional tool-specific Tcl header.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth-defines"></a>defines |  Preprocessor defines to pass to the synthesis frontend.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_synth-liberty"></a>liberty |  Optional Liberty standard-cell library for technology mapping.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth-opts"></a>opts |  Tool-specific synthesis frontend options.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_synth-params"></a>params |  Top-level Verilog module parameter overrides.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_synth-runner_flags"></a>runner_flags |  Command-line flags forwarded to Verilog Runner.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_synth-tool"></a>tool |  Synthesis tool plugin to use.   | String | required |  |
| <a id="rule_verilog_synth-top"></a>top |  Top-level module; defaults to the sole dependency's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_synth-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_synth-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog Runner synthesis plugins to load from this workspace.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:yosys.py"]`  |
| <a id="rule_verilog_synth-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner:verilog_runner.py"`  |


<a id="rule_verilog_synth_sandbox"></a>

## rule_verilog_synth_sandbox

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "rule_verilog_synth_sandbox")

rule_verilog_synth_sandbox(<a href="#rule_verilog_synth_sandbox-name">name</a>, <a href="#rule_verilog_synth_sandbox-deps">deps</a>, <a href="#rule_verilog_synth_sandbox-data">data</a>, <a href="#rule_verilog_synth_sandbox-clock_period_ps">clock_period_ps</a>, <a href="#rule_verilog_synth_sandbox-custom_tcl_body">custom_tcl_body</a>, <a href="#rule_verilog_synth_sandbox-custom_tcl_header">custom_tcl_header</a>,
                           <a href="#rule_verilog_synth_sandbox-defines">defines</a>, <a href="#rule_verilog_synth_sandbox-liberty">liberty</a>, <a href="#rule_verilog_synth_sandbox-opts">opts</a>, <a href="#rule_verilog_synth_sandbox-params">params</a>, <a href="#rule_verilog_synth_sandbox-runner_flags">runner_flags</a>, <a href="#rule_verilog_synth_sandbox-tool">tool</a>, <a href="#rule_verilog_synth_sandbox-top">top</a>,
                           <a href="#rule_verilog_synth_sandbox-verilog_runner_data">verilog_runner_data</a>, <a href="#rule_verilog_synth_sandbox-verilog_runner_env">verilog_runner_env</a>, <a href="#rule_verilog_synth_sandbox-verilog_runner_plugins">verilog_runner_plugins</a>,
                           <a href="#rule_verilog_synth_sandbox-verilog_runner_tool">verilog_runner_tool</a>)
</pre>

Writes logic-synthesis inputs and generated scripts into a tarball for independent execution outside Bazel.

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="rule_verilog_synth_sandbox-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |
| <a id="rule_verilog_synth_sandbox-deps"></a>deps |  Verilog libraries containing the design to synthesize.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_synth_sandbox-data"></a>data |  Additional runtime files needed by the synthesis plugin.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `[]`  |
| <a id="rule_verilog_synth_sandbox-clock_period_ps"></a>clock_period_ps |  Optional target clock period in picoseconds; requires liberty.   | Integer | optional |  `0`  |
| <a id="rule_verilog_synth_sandbox-custom_tcl_body"></a>custom_tcl_body |  Optional tool-specific Tcl body.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth_sandbox-custom_tcl_header"></a>custom_tcl_header |  Optional tool-specific Tcl header.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth_sandbox-defines"></a>defines |  Preprocessor defines to pass to the synthesis frontend.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_synth_sandbox-liberty"></a>liberty |  Optional Liberty standard-cell library for technology mapping.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth_sandbox-opts"></a>opts |  Tool-specific synthesis frontend options.   | List of strings | optional |  `[]`  |
| <a id="rule_verilog_synth_sandbox-params"></a>params |  Top-level Verilog module parameter overrides.   | <a href="https://bazel.build/rules/lib/core/dict">Dictionary: String -> String</a> | optional |  `{}`  |
| <a id="rule_verilog_synth_sandbox-runner_flags"></a>runner_flags |  Command-line flags forwarded to Verilog Runner.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//bazel:runner_flags"`  |
| <a id="rule_verilog_synth_sandbox-tool"></a>tool |  Synthesis tool plugin to use.   | String | required |  |
| <a id="rule_verilog_synth_sandbox-top"></a>top |  Top-level module; defaults to the sole dependency's label name.   | String | optional |  `""`  |
| <a id="rule_verilog_synth_sandbox-verilog_runner_data"></a>verilog_runner_data |  Additional Verilog Runner files needed at runtime.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner:verilog_runner_data"]`  |
| <a id="rule_verilog_synth_sandbox-verilog_runner_env"></a>verilog_runner_env |  Optional shell script sourced immediately before each Verilog Runner invocation.<br><br>The wrapper does not change directories before sourcing the hook, so it inherits the wrapper's existing working directory. Direct wrappers add the hook to runfiles and source its runfiles path; sandbox generator actions declare it as an input and source its execroot path. A direct hook is sourced before the wrapper unsets any inherited `rlocation` function, but callers needing runfiles lookup must initialize a working runfiles library rather than assume that Bazel exports a usable `rlocation` implementation. Bedrock appends its `verilog_runner_plugins` directories to `VERILOG_RUNNER_PLUGIN_PATH` after the hook runs. The hook is not included in sandbox archives or sourced by their final runners.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `None`  |
| <a id="rule_verilog_synth_sandbox-verilog_runner_plugins"></a>verilog_runner_plugins |  Verilog Runner synthesis plugins to load from this workspace.   | <a href="https://bazel.build/concepts/labels">List of labels</a> | optional |  `["@bedrock-rtl//python/verilog_runner/plugins:yosys.py"]`  |
| <a id="rule_verilog_synth_sandbox-verilog_runner_tool"></a>verilog_runner_tool |  The Verilog Runner tool to use.   | <a href="https://bazel.build/concepts/labels">Label</a> | optional |  `"@bedrock-rtl//python/verilog_runner"`  |


<a id="runner_flags"></a>

## runner_flags

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "runner_flags")

runner_flags(<a href="#runner_flags-name">name</a>)
</pre>

Build configuration for Verilog Runner flags from command line

**ATTRIBUTES**


| Name  | Description | Type | Mandatory | Default |
| :------------- | :------------- | :------------- | :------------- | :------------- |
| <a id="runner_flags-name"></a>name |  A unique name for this target.   | <a href="https://bazel.build/concepts/labels#target-names">Name</a> | required |  |


<a id="VerilogCoverageDataInfo"></a>

## VerilogCoverageDataInfo

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "VerilogCoverageDataInfo")

VerilogCoverageDataInfo(<a href="#VerilogCoverageDataInfo-toggle_info">toggle_info</a>, <a href="#VerilogCoverageDataInfo-line_info">line_info</a>, <a href="#VerilogCoverageDataInfo-branch_info">branch_info</a>, <a href="#VerilogCoverageDataInfo-expr_info">expr_info</a>, <a href="#VerilogCoverageDataInfo-covergroup_info">covergroup_info</a>, <a href="#VerilogCoverageDataInfo-user_info">user_info</a>,
                        <a href="#VerilogCoverageDataInfo-coverage_data">coverage_data</a>, <a href="#VerilogCoverageDataInfo-coverage_failures">coverage_failures</a>)
</pre>

Verilator raw coverage data and info artifacts.

**FIELDS**

| Name  | Description |
| :------------- | :------------- |
| <a id="VerilogCoverageDataInfo-toggle_info"></a>toggle_info |  -    |
| <a id="VerilogCoverageDataInfo-line_info"></a>line_info |  -    |
| <a id="VerilogCoverageDataInfo-branch_info"></a>branch_info |  -    |
| <a id="VerilogCoverageDataInfo-expr_info"></a>expr_info |  -    |
| <a id="VerilogCoverageDataInfo-covergroup_info"></a>covergroup_info |  -    |
| <a id="VerilogCoverageDataInfo-user_info"></a>user_info |  -    |
| <a id="VerilogCoverageDataInfo-coverage_data"></a>coverage_data |  -    |
| <a id="VerilogCoverageDataInfo-coverage_failures"></a>coverage_failures |  -    |


<a id="VerilogCoverageReportInfo"></a>

## VerilogCoverageReportInfo

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "VerilogCoverageReportInfo")

VerilogCoverageReportInfo(<a href="#VerilogCoverageReportInfo-toggle_info">toggle_info</a>, <a href="#VerilogCoverageReportInfo-line_info">line_info</a>, <a href="#VerilogCoverageReportInfo-branch_info">branch_info</a>, <a href="#VerilogCoverageReportInfo-expr_info">expr_info</a>, <a href="#VerilogCoverageReportInfo-covergroup_info">covergroup_info</a>,
                          <a href="#VerilogCoverageReportInfo-user_info">user_info</a>, <a href="#VerilogCoverageReportInfo-coverage_data">coverage_data</a>, <a href="#VerilogCoverageReportInfo-coverage_failures">coverage_failures</a>, <a href="#VerilogCoverageReportInfo-srcs">srcs</a>)
</pre>

Coverview coverage info and Verilator coverage data artifacts.

**FIELDS**

| Name  | Description |
| :------------- | :------------- |
| <a id="VerilogCoverageReportInfo-toggle_info"></a>toggle_info |  -    |
| <a id="VerilogCoverageReportInfo-line_info"></a>line_info |  -    |
| <a id="VerilogCoverageReportInfo-branch_info"></a>branch_info |  -    |
| <a id="VerilogCoverageReportInfo-expr_info"></a>expr_info |  -    |
| <a id="VerilogCoverageReportInfo-covergroup_info"></a>covergroup_info |  -    |
| <a id="VerilogCoverageReportInfo-user_info"></a>user_info |  -    |
| <a id="VerilogCoverageReportInfo-coverage_data"></a>coverage_data |  -    |
| <a id="VerilogCoverageReportInfo-coverage_failures"></a>coverage_failures |  -    |
| <a id="VerilogCoverageReportInfo-srcs"></a>srcs |  -    |


<a id="VerilogRunnerFlagsInfo"></a>

## VerilogRunnerFlagsInfo

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "VerilogRunnerFlagsInfo")

VerilogRunnerFlagsInfo(<a href="#VerilogRunnerFlagsInfo-name">name</a>, <a href="#VerilogRunnerFlagsInfo-runner_flags">runner_flags</a>)
</pre>

Verilog Runner flags provider

**FIELDS**

| Name  | Description |
| :------------- | :------------- |
| <a id="VerilogRunnerFlagsInfo-name"></a>name |  -    |
| <a id="VerilogRunnerFlagsInfo-runner_flags"></a>runner_flags |  -    |


<a id="extra_tags"></a>

## extra_tags

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "extra_tags")

extra_tags(<a href="#extra_tags-kind">kind</a>, <a href="#extra_tags-tool">tool</a>)
</pre>

Returns a list of extra tags that should be added to a target.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="extra_tags-kind"></a>kind |  The kind of target.   |  none |
| <a id="extra_tags-tool"></a>tool |  The tool name.   |  none |

**RETURNS**

A list of extra tags. Specifically:
      * The kind of target -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<kind>
      * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
      * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.


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


<a id="is_param_combination_legal"></a>

## is_param_combination_legal

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "is_param_combination_legal")

is_param_combination_legal(<a href="#is_param_combination_legal-params">params</a>, <a href="#is_param_combination_legal-illegal_param_combinations">illegal_param_combinations</a>)
</pre>

Checks if a given combination of parameters is legal based on the provided illegal combinations.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="is_param_combination_legal-params"></a>params |  A dictionary where keys are parameter names and values are the specific value for those parameters in the current combination.   |  none |
| <a id="is_param_combination_legal-illegal_param_combinations"></a>illegal_param_combinations |  A dictionary where keys are tuples of parameter names and values are lists of tuples of illegal values for those parameters.   |  none |

**RETURNS**

True if the combination is legal, False if it is illegal.


<a id="verilog_elab_and_lint_test_suite"></a>

## verilog_elab_and_lint_test_suite

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_elab_and_lint_test_suite")

verilog_elab_and_lint_test_suite(<a href="#verilog_elab_and_lint_test_suite-name">name</a>, <a href="#verilog_elab_and_lint_test_suite-top">top</a>, <a href="#verilog_elab_and_lint_test_suite-deps">deps</a>, <a href="#verilog_elab_and_lint_test_suite-defines">defines</a>, <a href="#verilog_elab_and_lint_test_suite-params">params</a>, <a href="#verilog_elab_and_lint_test_suite-elab_tools">elab_tools</a>, <a href="#verilog_elab_and_lint_test_suite-lint_tool">lint_tool</a>,
                                 <a href="#verilog_elab_and_lint_test_suite-disable_lint_rules">disable_lint_rules</a>, <a href="#verilog_elab_and_lint_test_suite-kwargs">**kwargs</a>)
</pre>

Creates a suite of Verilog elaboration and lint tests for each combination of the provided parameters.

The function generates a wrapper covering all possible combinations of the provided parameters, creates a
verilog_elab_test for each elaboration tool, and creates one verilog_lint_test. Elaboration test names append
the tool name followed by "_elab_test"; the lint test name appends "_lint_test".


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_elab_and_lint_test_suite-name"></a>name |  The base name for the test suite.   |  none |
| <a id="verilog_elab_and_lint_test_suite-top"></a>top |  The top-level module to instantiate. Can be left undefined if there is only one dependency.   |  `None` |
| <a id="verilog_elab_and_lint_test_suite-deps"></a>deps |  The dependencies of the test suite.   |  `[]` |
| <a id="verilog_elab_and_lint_test_suite-defines"></a>defines |  A list of defines.   |  `[]` |
| <a id="verilog_elab_and_lint_test_suite-params"></a>params |  A dictionary where keys are parameter names and values are lists of possible values for those parameters.   |  `{}` |
| <a id="verilog_elab_and_lint_test_suite-elab_tools"></a>elab_tools |  The tools to use for elaboration. Defaults to Verific and Slang.   |  `["verific", "slang"]` |
| <a id="verilog_elab_and_lint_test_suite-lint_tool"></a>lint_tool |  The tool to use for linting.   |  `"ascentlint"` |
| <a id="verilog_elab_and_lint_test_suite-disable_lint_rules"></a>disable_lint_rules |  A list of lint rules to disable in the generated files.   |  `[]` |
| <a id="verilog_elab_and_lint_test_suite-kwargs"></a>kwargs |  Additional common keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.   |  none |


<a id="verilog_elab_test"></a>

## verilog_elab_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_elab_test")

verilog_elab_test(<a href="#verilog_elab_test-name">name</a>, <a href="#verilog_elab_test-tool">tool</a>, <a href="#verilog_elab_test-tags">tags</a>, <a href="#verilog_elab_test-kwargs">**kwargs</a>)
</pre>

Wraps rule_verilog_elab_test and appends extra tags.

The following extra tags are unconditionally appended to the list of tags:
    * elab -- useful for test filtering, e.g., bazel test //... --test_tag_filters=elab
    * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
    * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
    * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_elab_test-name"></a>name |  test name   |  none |
| <a id="verilog_elab_test-tool"></a>tool |  The elaboration tool to use.   |  none |
| <a id="verilog_elab_test-tags"></a>tags |  The tags to add to the test.   |  `[]` |
| <a id="verilog_elab_test-kwargs"></a>kwargs |  Other arguments to pass to the rule_verilog_elab_test rule.   |  none |


<a id="verilog_fpv_test"></a>

## verilog_fpv_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_fpv_test")

verilog_fpv_test(<a href="#verilog_fpv_test-tool">tool</a>, <a href="#verilog_fpv_test-tags">tags</a>, <a href="#verilog_fpv_test-kwargs">**kwargs</a>)
</pre>

Wraps rule_verilog_fpv_test with a default tool and appends extra tags.

The following extra tags are unconditionally appended to the list of tags:
    * fpv -- useful for test filtering, e.g., bazel test //... --test_tag_filters=fpv
    * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
    * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
    * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_fpv_test-tool"></a>tool |  The formal verification tool to use.   |  none |
| <a id="verilog_fpv_test-tags"></a>tags |  The tags to add to the test.   |  `[]` |
| <a id="verilog_fpv_test-kwargs"></a>kwargs |  Other arguments to pass to the rule_verilog_fpv_test rule.   |  none |


<a id="verilog_fpv_test_suite"></a>

## verilog_fpv_test_suite

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_fpv_test_suite")

verilog_fpv_test_suite(<a href="#verilog_fpv_test_suite-name">name</a>, <a href="#verilog_fpv_test_suite-defines">defines</a>, <a href="#verilog_fpv_test_suite-params">params</a>, <a href="#verilog_fpv_test_suite-illegal_param_combinations">illegal_param_combinations</a>, <a href="#verilog_fpv_test_suite-sandbox">sandbox</a>,
                       <a href="#verilog_fpv_test_suite-verilog_fpv_test_func">verilog_fpv_test_func</a>, <a href="#verilog_fpv_test_suite-verilog_fpv_sandbox_func">verilog_fpv_sandbox_func</a>, <a href="#verilog_fpv_test_suite-kwargs">**kwargs</a>)
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
| <a id="verilog_fpv_test_suite-illegal_param_combinations"></a>illegal_param_combinations |  A dictionary where keys are parameter tuples and values are lists of illegal values for those parameters.   |  `{}` |
| <a id="verilog_fpv_test_suite-sandbox"></a>sandbox |  Whether to create a sandbox for the test.   |  `True` |
| <a id="verilog_fpv_test_suite-verilog_fpv_test_func"></a>verilog_fpv_test_func |  A function to use instead of verilog_fpv_test.   |  `None` |
| <a id="verilog_fpv_test_suite-verilog_fpv_sandbox_func"></a>verilog_fpv_sandbox_func |  A function to use instead of rule_verilog_fpv_sandbox.   |  `None` |
| <a id="verilog_fpv_test_suite-kwargs"></a>kwargs |  Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.   |  none |


<a id="verilog_lint_test"></a>

## verilog_lint_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_lint_test")

verilog_lint_test(<a href="#verilog_lint_test-tool">tool</a>, <a href="#verilog_lint_test-tags">tags</a>, <a href="#verilog_lint_test-kwargs">**kwargs</a>)
</pre>

Wraps rule_verilog_lint_test with a default tool and appends extra tags.

The following extra tags are unconditionally appended to the list of tags:
    * lint -- useful for test filtering, e.g., bazel test //... --test_tag_filters=lint
    * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
    * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
    * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_lint_test-tool"></a>tool |  The lint tool to use.   |  none |
| <a id="verilog_lint_test-tags"></a>tags |  The tags to add to the test.   |  `[]` |
| <a id="verilog_lint_test-kwargs"></a>kwargs |  Other arguments to pass to the rule_verilog_lint_test rule.   |  none |


<a id="verilog_sim_coverage_aggregate"></a>

## verilog_sim_coverage_aggregate

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_sim_coverage_aggregate")

verilog_sim_coverage_aggregate(<a href="#verilog_sim_coverage_aggregate-name">name</a>, <a href="#verilog_sim_coverage_aggregate-coverage_data">coverage_data</a>, <a href="#verilog_sim_coverage_aggregate-coverage_reports">coverage_reports</a>, <a href="#verilog_sim_coverage_aggregate-deps">deps</a>, <a href="#verilog_sim_coverage_aggregate-all_srcs">all_srcs</a>, <a href="#verilog_sim_coverage_aggregate-kwargs">**kwargs</a>)
</pre>

Wraps rule_verilog_sim_coverage_aggregate.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_sim_coverage_aggregate-name"></a>name |  The name of the aggregate coverage target.   |  none |
| <a id="verilog_sim_coverage_aggregate-coverage_data"></a>coverage_data |  Coverage data targets whose info files should be merged.   |  `[]` |
| <a id="verilog_sim_coverage_aggregate-coverage_reports"></a>coverage_reports |  Coverage report targets whose transitive info files should be merged.   |  `[]` |
| <a id="verilog_sim_coverage_aggregate-deps"></a>deps |  The dependencies of the testbench whose design sources should be included in sources.txt.   |  `[]` |
| <a id="verilog_sim_coverage_aggregate-all_srcs"></a>all_srcs |  List of all source files that should be included in the coverage report.   |  `None` |
| <a id="verilog_sim_coverage_aggregate-kwargs"></a>kwargs |  Other arguments to pass to the rule_verilog_sim_coverage_aggregate rule.   |  none |


<a id="verilog_sim_coverage_data"></a>

## verilog_sim_coverage_data

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_sim_coverage_data")

verilog_sim_coverage_data(<a href="#verilog_sim_coverage_data-tool">tool</a>, <a href="#verilog_sim_coverage_data-opts">opts</a>, <a href="#verilog_sim_coverage_data-elab_opts">elab_opts</a>, <a href="#verilog_sim_coverage_data-sim_opts">sim_opts</a>, <a href="#verilog_sim_coverage_data-tags">tags</a>, <a href="#verilog_sim_coverage_data-waves">waves</a>, <a href="#verilog_sim_coverage_data-kwargs">**kwargs</a>)
</pre>

Wraps rule_verilog_sim_coverage_data.

**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_sim_coverage_data-tool"></a>tool |  The simulation tool to use. Must be "verilator".   |  none |
| <a id="verilog_sim_coverage_data-opts"></a>opts |  Deprecated VCS-only simulation options.   |  `[]` |
| <a id="verilog_sim_coverage_data-elab_opts"></a>elab_opts |  Tool-specific compile/elaboration options not covered by other arguments.   |  `[]` |
| <a id="verilog_sim_coverage_data-sim_opts"></a>sim_opts |  Tool-specific simulation runtime options, such as simulator plusargs.   |  `[]` |
| <a id="verilog_sim_coverage_data-tags"></a>tags |  <p align="center"> - </p>   |  `[]` |
| <a id="verilog_sim_coverage_data-waves"></a>waves |  Enable waveform dumping.   |  `False` |
| <a id="verilog_sim_coverage_data-kwargs"></a>kwargs |  Other arguments to pass to the rule_verilog_sim_coverage_data rule.   |  none |


<a id="verilog_sim_test"></a>

## verilog_sim_test

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_sim_test")

verilog_sim_test(<a href="#verilog_sim_test-tool">tool</a>, <a href="#verilog_sim_test-opts">opts</a>, <a href="#verilog_sim_test-elab_opts">elab_opts</a>, <a href="#verilog_sim_test-sim_opts">sim_opts</a>, <a href="#verilog_sim_test-tags">tags</a>, <a href="#verilog_sim_test-waves">waves</a>, <a href="#verilog_sim_test-kwargs">**kwargs</a>)
</pre>

Wraps rule_verilog_sim_test with a default tool and appends extra tags.

The following extra tags are unconditionally appended to the list of tags:
    * sim -- useful for test filtering, e.g., bazel test //... --test_tag_filters=sim
    * The tool name -- useful for test filtering, e.g., bazel test //... --test_tag_filters=<tool>
    * resources:verilog_test_tool_licenses_<tool>:1 -- only if the tool appears in TOOLS_THAT_NEED_LICENSES.
    * no-sandbox -- Loosens some Bazel hermeticity features so that undeclared EDA tool test outputs are preserved for debugging.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_sim_test-tool"></a>tool |  The simulation tool to use.   |  none |
| <a id="verilog_sim_test-opts"></a>opts |  Deprecated VCS-only simulation options.   |  `[]` |
| <a id="verilog_sim_test-elab_opts"></a>elab_opts |  Tool-specific compile/elaboration options not covered by other arguments.   |  `[]` |
| <a id="verilog_sim_test-sim_opts"></a>sim_opts |  Tool-specific simulation runtime options, such as simulator plusargs.   |  `[]` |
| <a id="verilog_sim_test-tags"></a>tags |  The tags to add to the test.   |  `[]` |
| <a id="verilog_sim_test-waves"></a>waves |  Enable waveform dumping.   |  `False` |
| <a id="verilog_sim_test-kwargs"></a>kwargs |  Other arguments to pass to the rule_verilog_sim_test rule.   |  none |


<a id="verilog_sim_test_suite"></a>

## verilog_sim_test_suite

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_sim_test_suite")

verilog_sim_test_suite(<a href="#verilog_sim_test_suite-name">name</a>, <a href="#verilog_sim_test_suite-defines">defines</a>, <a href="#verilog_sim_test_suite-params">params</a>, <a href="#verilog_sim_test_suite-illegal_param_combinations">illegal_param_combinations</a>, <a href="#verilog_sim_test_suite-coverage">coverage</a>, <a href="#verilog_sim_test_suite-kwargs">**kwargs</a>)
</pre>

Creates a suite of Verilog sim tests for each combination of the provided parameters.

The function generates all possible combinations of the provided parameters and creates a verilog_sim_test
for each combination. The test names are generated by appending "_sim_test"
to the base name followed by the parameter key-values.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_sim_test_suite-name"></a>name |  The base name for the test suite.   |  none |
| <a id="verilog_sim_test_suite-defines"></a>defines |  A list of defines.   |  `[]` |
| <a id="verilog_sim_test_suite-params"></a>params |  A dictionary where keys are parameter names and values are lists of possible values for those parameters.   |  `{}` |
| <a id="verilog_sim_test_suite-illegal_param_combinations"></a>illegal_param_combinations |  A dictionary where keys are parameter tuples and values are lists of tuples of illegal values for those parameters.   |  `{}` |
| <a id="verilog_sim_test_suite-coverage"></a>coverage |  Value enabling and disabling coverage data.   |  `False` |
| <a id="verilog_sim_test_suite-kwargs"></a>kwargs |  Additional keyword arguments to be passed to the verilog_elab_test and verilog_lint_test functions.   |  none |


<a id="verilog_synth"></a>

## verilog_synth

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_synth")

verilog_synth(<a href="#verilog_synth-name">name</a>, <a href="#verilog_synth-tool">tool</a>, <a href="#verilog_synth-tags">tags</a>, <a href="#verilog_synth-kwargs">**kwargs</a>)
</pre>

Creates a runnable logic-synthesis target that streams the raw tool report.

The tool string selects a Verilog Runner synthesis plugin, so callers can
use the bundled Yosys plugin or provide another open-source or proprietary
synthesis plugin through `verilog_runner_plugins`. The Yosys flow produces
technology-independent cell and logic-depth signals without a Liberty
library, and can optionally map against one when `liberty` is supplied.

Example:
    ```starlark
    verilog_synth(
        name = "fifo_synth",
        tool = "yosys",
        deps = [":fifo"],
        top = "fifo",
        params = {"Depth": "16", "Width": "32"},
    )
    ```


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_synth-name"></a>name |  Target name.   |  none |
| <a id="verilog_synth-tool"></a>tool |  Synthesis plugin name.   |  none |
| <a id="verilog_synth-tags"></a>tags |  Additional Bazel tags.   |  `[]` |
| <a id="verilog_synth-kwargs"></a>kwargs |  Arguments forwarded to rule_verilog_synth.   |  none |


<a id="verilog_synth_sandbox"></a>

## verilog_synth_sandbox

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_synth_sandbox")

verilog_synth_sandbox(<a href="#verilog_synth_sandbox-name">name</a>, <a href="#verilog_synth_sandbox-tool">tool</a>, <a href="#verilog_synth_sandbox-tags">tags</a>, <a href="#verilog_synth_sandbox-kwargs">**kwargs</a>)
</pre>

Creates a portable logic-synthesis reproduction archive.

The archive contains the transitive Verilog source and header closure,
Verilog Runner plugin files, and generated filelist, Tcl, and shell scripts.
The synthesis tool executable remains a system dependency.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_synth_sandbox-name"></a>name |  Target name.   |  none |
| <a id="verilog_synth_sandbox-tool"></a>tool |  Synthesis plugin name.   |  none |
| <a id="verilog_synth_sandbox-tags"></a>tags |  Additional Bazel tags.   |  `[]` |
| <a id="verilog_synth_sandbox-kwargs"></a>kwargs |  Arguments forwarded to rule_verilog_synth_sandbox.   |  none |


<a id="verilog_synth_suite"></a>

## verilog_synth_suite

<pre>
load("@bedrock-rtl//bazel:verilog.bzl", "verilog_synth_suite")

verilog_synth_suite(<a href="#verilog_synth_suite-name">name</a>, <a href="#verilog_synth_suite-defines">defines</a>, <a href="#verilog_synth_suite-params">params</a>, <a href="#verilog_synth_suite-illegal_param_combinations">illegal_param_combinations</a>, <a href="#verilog_synth_suite-library_name">library_name</a>, <a href="#verilog_synth_suite-sandbox">sandbox</a>,
                    <a href="#verilog_synth_suite-sandbox_tags">sandbox_tags</a>, <a href="#verilog_synth_suite-tags">tags</a>, <a href="#verilog_synth_suite-verilog_synth_func">verilog_synth_func</a>, <a href="#verilog_synth_suite-verilog_synth_sandbox_func">verilog_synth_sandbox_func</a>, <a href="#verilog_synth_suite-kwargs">**kwargs</a>)
</pre>

Creates runnable and reproducible synthesis targets for parameter combinations.

Each runnable target delegates to `verilog_synth` and uses a deterministic
name derived from its parameter values, tool, and mapping library. When
`sandbox` is true, a sibling target ending in `_sandbox` packages the same
inputs and generated scripts for execution outside Bazel.


**PARAMETERS**


| Name  | Description | Default Value |
| :------------- | :------------- | :------------- |
| <a id="verilog_synth_suite-name"></a>name |  Base name for generated targets.   |  none |
| <a id="verilog_synth_suite-defines"></a>defines |  Preprocessor defines for synthesis.   |  `[]` |
| <a id="verilog_synth_suite-params"></a>params |  Parameter names mapped to lists of values.   |  `{}` |
| <a id="verilog_synth_suite-illegal_param_combinations"></a>illegal_param_combinations |  Parameter tuples mapped to disallowed value tuples.   |  `{}` |
| <a id="verilog_synth_suite-library_name"></a>library_name |  Target-name identifier for the PDK/library/corner. Defaults to `nolib` when no Liberty file is supplied and is required when `liberty` is supplied.   |  `None` |
| <a id="verilog_synth_suite-sandbox"></a>sandbox |  Whether to create a reproduction archive beside each runnable target.   |  `True` |
| <a id="verilog_synth_suite-sandbox_tags"></a>sandbox_tags |  Tags for sandbox targets. Defaults to `tags`.   |  `None` |
| <a id="verilog_synth_suite-tags"></a>tags |  Tags for runnable targets.   |  `[]` |
| <a id="verilog_synth_suite-verilog_synth_func"></a>verilog_synth_func |  Runnable-target constructor override.   |  `None` |
| <a id="verilog_synth_suite-verilog_synth_sandbox_func"></a>verilog_synth_sandbox_func |  Sandbox-target constructor override.   |  `None` |
| <a id="verilog_synth_suite-kwargs"></a>kwargs |  Additional arguments passed to verilog_synth.   |  none |


