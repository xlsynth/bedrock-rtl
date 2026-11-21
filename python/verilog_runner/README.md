# Verilog Runner


Verilog Runner is a command-line tool designed to facilitate the execution of Verilog and SystemVerilog tests. It supports various subcommands for elaboration, linting, simulation, and formal property verification, and is extensible through plugins.

> **Note:** We use this as the backend implementation for several Bazel rules such as `rule_verilog_elab_test`, `rule_verilog_lint_test`, `rule_verilog_sim_test`, and `rule_verilog_fpv_test`.


## Features


- **Elaboration**: Static elaboration of Verilog designs.
- **Linting**: Code linting to ensure adherence to coding standards.
- **Simulation**: Running simulations with support for UVM and waveform dumping.
- **Formal Property Verification**: Verification of formal properties using supported tools.
- **Plugin Support**: Easily extendable with custom plugins for different EDA tools.

## Usage


Ensure you have Python 3.12 or later installed. You can then run the tool directly from the command line.

```bash
python3 verilog_runner.py --help
```


## Plugins


Verilog Runner uses a plugin architecture to support a variety of EDA tools. To create a plugin, implement the `EdaTool` abstract base class and specify the `subcommand` and `tool_name` attributes.

For example:

```python
class MyCustomElaborationTool(EdaTool):
    subcommand = Elab
    tool_name = "mycustomtool"
    # Implement the abstract methods of EdaTool
```


Verilog Runner discovers plugins by searching for Python modules in the directories specified by the `VERILOG_RUNNER_PLUGIN_PATH` environment variable.
The syntax of the environment variable is the same as the `PYTHONPATH` environment variable (a colon-separated list of directories).

If no plugins are found, Verilog Runner will exit with an error.

The public Slang plugin supports both elaboration and linting. Slang lint fully elaborates the design and accepts the existing `--policy` argument for a Slang command file; Bedrock's Bazel lint rule supplies its strict repository-owned policy by default.

## Yosys formal verification

The public `fpv --tool=yosys` plugin requires Yosys with the yosys-slang frontend,
SymbiYosys (`sby`), and the selected engine on `PATH`. `YOSYS_PATH` and `SBY_PATH`
can select alternative executables. The default runs an unbounded safety proof
with `abc pdr` and a 60-second SBY timeout. The default SBY depth setting is 20
for depth-based engines and modes. Set `opts` entries to
`mode=prove`, `mode=bmc`, or `mode=cover`, `engine=<engine and arguments>`,
`depth=<positive integer>`, and `timeout=<seconds>`. BMC and cover default to
`smtbmc z3`. Frontend flags use `analysis_opts` and `elab_opts`.

Clock and reset assumptions are supplied by the harness. The backend uses SBY's
default single-clock model. It retains the generated RTLIL model, SBY configuration,
native result directory, and console log. Repeated runs back up the prior SBY
result directory. `elab_only` emits the model without running an engine.
