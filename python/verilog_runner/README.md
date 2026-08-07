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

## SBY Formal Plugin

The in-tree `sby` plugin implements the `fpv` subcommand using SymbiYosys, Yosys with yosys-slang, and Yices.
The repository Docker image installs the compatible toolchain, and the Bazel FPV rules package the plugin automatically; `VERILOG_RUNNER_PLUGIN_PATH` is only needed for additional external plugins.

By default, one invocation generates and runs two SBY tasks:

- `prove` uses unbounded safety mode.
- `cover` uses bounded cover mode with depth 20.

Both tasks use `smtbmc yices`, and every task must write a `PASS` status for the Verilog Runner test to pass.
SBY logs, status files, traces, and other diagnostics remain in `<control-stem>_sby_<task>` directories, while combined console output is written to the Bazel-provided log file.

Setting `elab_only = True` selects one `elab` task in SBY `mode prep`.
This runs yosys-slang analysis and Yosys hierarchy/preparation without configuring or running a solver.
The SBY plugin rejects `gui` and `conn`, which are modes provided only by some proprietary FPV plugins.

The FPV option channels have the following SBY meanings:

- `analysis_opts` are appended to `read_slang`.
- `elab_opts` are appended to the Yosys `hierarchy` command.
- Legacy `opts` are also treated as yosys-slang analysis options for compatibility.

Files passed through the Bazel `data` attribute are included in the SBY `[files]` section at their workspace-relative paths, so `$readmemh` and `$readmemb` can find them.
The tool-neutral `custom_control_header` and `custom_control_body` attributes accept `.tcl` or `.sby` fragments.
For SBY, the header fragment may add SBY configuration sections, while the body fragment contains Yosys commands inside `[script]` and replaces the default `prep -top` command.
Tcl-based tools may instead use the equivalent `custom_tcl_header` and `custom_tcl_body` aliases with `.tcl` fragments; specifying both spellings for one fragment is an error, and SBY rejects the Tcl-specific spelling.

Bedrock's `br_verilog_fpv_test_suite` wrapper defines `BR_YOSYS_SBY` for SBY targets.
That profile disables unsupported concurrent Bedrock SVA without globally disabling immediate/combinational FPV checks; harnesses must still use constructs accepted by yosys-slang.
Direct Verilog Runner users must pass `BR_YOSYS_SBY` explicitly when compiling Bedrock assertion macros.
