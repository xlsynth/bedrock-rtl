# Copyright 2024-2025 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Plugin discovery for Verilog Runner."""

import logging
import inspect
import importlib.util
import os
import re
import sys
from eda_tool import EdaTool
from cli import Subcommand
from typing import Dict, List, Tuple, Type

# Currently we only support a single version of the plugin API at a time.
# We check for plugin compatibility at import time by checking versions are equal.
#
# The version number is used as a simple semantic versioning check.
#
# From https://semver.org:
#   Given a version number MAJOR.MINOR.PATCH, increment the:
#   1. MAJOR version when you make incompatible API changes
#   2. MINOR version when you add functionality in a backward compatible manner
#   3. PATCH version when you make backward compatible bug fixes
#
# Plugins must satisfy the following constraints:
#   - The plugin MAJOR version must match this runner's MAJOR version exactly.
#   - The plugin MINOR version must match this runner's MINOR version exactly.
#   - The plugin PATCH version must be greater than or equal to this runner's PATCH version.
PLUGIN_API_VERSION = "2.0.0"


def parse_plugin_api_version(version: str) -> Tuple[int, int, int]:
    """
    Parses a semantic version string (MAJOR.MINOR.PATCH) and returns a tuple of integers.
    Raises ValueError if the version string is invalid.
    """
    match = re.match(r"^(\d+)\.(\d+)\.(\d+)$", version)
    if not match:
        raise ValueError(f"Invalid version string: {version}")
    return tuple(int(part) for part in match.groups())


def is_plugin_compatible(runner_version: str, plugin_version: str) -> bool:
    """
    Checks if the runner is compatible with a plugin using the semantic versioning rules outlined above.

    Compatibility rule (per semantic versioning):
      - The MAJOR versions must match.
      - The MINOR versions must match.
      - The plugin patch version must be greater than or equal to the runner's patch version.
    """
    runner_version_tuple = parse_plugin_api_version(runner_version)
    plugin_version_tuple = parse_plugin_api_version(plugin_version)
    # Check MAJOR version compatibility.
    if runner_version_tuple[0] != plugin_version_tuple[0]:
        return False
    # Check MINOR version compatibility.
    if runner_version_tuple[1] != plugin_version_tuple[1]:
        return False
    # Check PATCH version compatibility.
    if runner_version_tuple[2] > plugin_version_tuple[2]:
        return False
    return True


def check_plugin_api_version(module: object) -> bool:
    """Return true if the plugin API version is compatible."""
    if not hasattr(module, "PLUGIN_API_VERSION"):
        logging.warning(
            f"Plugin module {module.__name__} does not have a PLUGIN_API_VERSION."
        )
        return False
    if not is_plugin_compatible(
        runner_version=PLUGIN_API_VERSION, plugin_version=module.PLUGIN_API_VERSION
    ):
        logging.warning(
            f"Plugin module {module.__name__} has an incompatible PLUGIN_API_VERSION: {module.PLUGIN_API_VERSION}."
        )
        return False
    return True


def discover_plugins(
    plugin_dirs: List[str], allowed_subcommands: Tuple[Type[Subcommand]]
) -> Dict[Type[Subcommand], Dict[str, Type["EdaTool"]]]:
    """Discover plugins and organize them by subcommand and tool."""
    logging.info(f"PLUGIN_API_VERSION: {PLUGIN_API_VERSION}")
    logging.info(f"Searching plugin directories: {plugin_dirs}")
    plugin_files = collect_plugin_files(plugin_dirs)
    logging.info(f"Found plugin files: {plugin_files}")
    modules = import_plugin_modules(plugin_files)
    plugins = extract_plugin_classes(modules)
    plugins_by_subcommand = organize_plugins(plugins, allowed_subcommands)
    logging.info(f"Found and imported plugins: {plugins_by_subcommand}")
    return plugins_by_subcommand


def collect_plugin_files(plugin_dirs: List[str]) -> List[str]:
    """Collect all Python plugin files from the specified directories."""
    plugin_files = []
    for directory in plugin_dirs:
        if not os.path.exists(directory):
            logging.warning(f"{directory} does not exist. Skipping.")
        elif not os.path.isdir(directory):
            logging.warning(f"{directory} is not a directory. Skipping.")
        else:
            for filename in os.listdir(directory):
                if filename.endswith(".py") and not filename.startswith("__"):
                    file_path = os.path.join(directory, filename)
                    plugin_files.append(file_path)
    return plugin_files


def import_plugin_modules(plugin_files: List[str]) -> List[object]:
    """Import modules from the given list of plugin file paths."""
    modules = []
    for file_path in plugin_files:
        directory, filename = os.path.split(file_path)
        module_name = os.path.splitext(filename)[0]
        sys.path.insert(0, directory)  # Temporarily add directory to sys.path
        try:
            module = importlib.import_module(module_name)
            if check_plugin_api_version(module):
                modules.append(module)
            else:
                logging.warning(f"Skipping import of plugin module {module_name}.")
        except Exception as e:
            logging.warning(f"Failed to load plugin module {module_name}: {e}")
        finally:
            sys.path.pop(0)  # Remove directory from sys.path
    return modules


def extract_plugin_classes(modules: List[object]) -> List[Type["EdaTool"]]:
    """Extract plugin classes inheriting from EdaTool from the imported modules."""
    plugins = []
    for module in modules:
        for attr_name in dir(module):
            attr = getattr(module, attr_name)
            if (
                inspect.isclass(attr)
                and issubclass(attr, EdaTool)
                and attr is not EdaTool
            ):
                plugins.append(attr)
    return plugins


def organize_plugins(
    plugins: List[Type["EdaTool"]], allowed_subcommands: Tuple[Type[Subcommand]]
) -> Dict[Type[Subcommand], Dict[str, Type["EdaTool"]]]:
    """Organize plugins into a dictionary by subcommand and tool_name."""
    plugins_by_subcommand = {}
    for plugin_class in plugins:
        subcommand = getattr(plugin_class, "subcommand", None)
        tool_name = getattr(plugin_class, "tool_name", None)
        if subcommand and tool_name:
            if subcommand in allowed_subcommands:
                if subcommand not in plugins_by_subcommand:
                    plugins_by_subcommand[subcommand] = {}
                plugins_by_subcommand[subcommand][tool_name] = plugin_class
            else:
                raise ValueError(
                    f"Plugin '{plugin_class.__name__}' uses an unsupported class for subcommand: '{subcommand}'."
                )
        else:
            raise ValueError(
                f"Plugin '{plugin_class.__name__}' missing 'subcommand' or 'tool_name' attributes."
            )
    return plugins_by_subcommand
