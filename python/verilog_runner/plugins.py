# Copyright 2024 The Bedrock-RTL Authors
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
import sys
from eda_tool import EdaTool
from cli import Subcommand
from typing import Dict, List, Tuple, Type

# Currently we only support a single version of the plugin API at a time.
# We check for plugin compatibility at import time by checking versions are equal.
#
# The version number is used as a simple semantic versioning check.
#
# Major version changes are definitely breaking.
# Minor version changes are intended to be non-breaking but we don't guarantee it.
PLUGIN_API_VERSION = "1.0"


def check_plugin_api_version(module: object) -> bool:
    """Return true if the plugin API version is compatible."""
    if not hasattr(module, "PLUGIN_API_VERSION"):
        logging.warning(
            f"Plugin module {module.__name__} does not have a PLUGIN_API_VERSION."
        )
        return False
    if module.PLUGIN_API_VERSION != PLUGIN_API_VERSION:
        logging.warning(
            f"Plugin module {module.__name__} has an invalid PLUGIN_API_VERSION: {module.PLUGIN_API_VERSION}."
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
            raise ValueError(f"{directory} does not exist.")
        if not os.path.isdir(directory):
            raise ValueError(f"{directory} is not a directory.")
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
            logging.error(f"Failed to load plugin module {module_name}: {e}")
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
