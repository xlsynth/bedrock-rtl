# SPDX-License-Identifier: Apache-2.0


"""Unit tests for the util module."""

import argparse
import unittest
import logging
import tempfile
import os
from python.verilog_runner.util import (
    get_class_logger,
    wrap_text,
    dump_file,
    print_greeting,
    print_summary,
    check_filename_extension,
    gen_file_header,
    include_dirs,
    generate_random_seed,
    to_filelist,
    write_and_dump_file,
    run_shell_script,
    check_simulation_success,
    format_table,
)


class TestUtilFunctions(unittest.TestCase):

    def test_get_class_logger(self):
        logger = get_class_logger("test_subcommand", "test_tool")
        self.assertIsInstance(logger, logging.LoggerAdapter)

    def test_wrap_text(self):
        text = "This is a sample text that needs to be wrapped."
        wrapped_text = wrap_text(text, width=10)
        self.assertIn("\n", wrapped_text)

    def test_dump_file(self):
        with tempfile.NamedTemporaryFile(delete=False) as temp_file:
            temp_file.write(b"Line 1\nLine 2\nLine 3\n")
            temp_filename = temp_file.name

        logger = logging.getLogger("test_logger")
        with self.assertLogs(logger, level="INFO") as log:
            dump_file(temp_filename, logger)
            self.assertIn("Dumping", log.output[0])

        os.remove(temp_filename)

    def test_check_filename_extension(self):
        self.assertEqual(check_filename_extension("test.v", (".v", ".sv")), "test.v")
        with self.assertRaises(argparse.ArgumentTypeError):
            check_filename_extension("test.txt", (".v", ".sv"))
        self.assertEqual(
            check_filename_extension("test.foo", (".v", ".sv"), error=False), "test.foo"
        )

    def test_gen_file_header(self):
        header = gen_file_header("test.v", "test_tool")
        self.assertIn("# test.v", header)
        self.assertIn("Auto-generated", header)

    def test_include_dirs(self):
        hdrs = ["dir1/file1.h", "dir2/file2.h", "dir1/file3.h"]
        dirs = include_dirs(hdrs)
        self.assertEqual(set(dirs), {"dir1", "dir2"})

    def test_generate_random_seed(self):
        seed = generate_random_seed()
        self.assertIsInstance(seed, int)

    def test_to_filelist(self):
        srcs = ["file1.v", "file2.v"]
        filelist = to_filelist(srcs)
        self.assertEqual(filelist, "file1.v\nfile2.v\n")

    def test_write_and_dump_file(self):
        logger = logging.getLogger("test_logger")
        content = "Sample content"
        with tempfile.NamedTemporaryFile(delete=False) as temp_file:
            temp_filename = temp_file.name

        with self.assertLogs(logger, level="INFO") as log:
            write_and_dump_file(content, temp_filename, logger)
            self.assertIn("Writing", log.output[0])

        os.remove(temp_filename)

    def test_run_shell_script(self):
        logger = logging.getLogger("test_logger")
        with tempfile.NamedTemporaryFile(delete=False, mode="w") as temp_file:
            temp_file.write("echo 'Hello World'")
            temp_filename = temp_file.name

        return_code, output = run_shell_script(temp_filename, logger)
        self.assertEqual(return_code, 0)
        self.assertIn("Hello World", output)

        os.remove(temp_filename)

    def test_check_simulation_success(self):
        success_criteria = check_simulation_success(0, False, "TEST PASSED")
        self.assertTrue(success_criteria["Return code 0"])
        self.assertTrue(
            success_criteria[
                "Output does not contain 'Bedrock-RTL assertion macro failed'"
            ]
        )
        self.assertTrue(success_criteria["Output contains 'TEST PASSED'"])

    def test_format_table_simple(self):
        headers = ["Name", "Age", "City"]
        rows = [["Alice", "30", "New York"], ["Bob", "25", "San Francisco"]]
        expected = (
            "+-------+-----+---------------+\n"
            "| Name  | Age | City          |\n"
            "+-------+-----+---------------+\n"
            "| Alice | 30  | New York      |\n"
            "+-------+-----+---------------+\n"
            "| Bob   | 25  | San Francisco |\n"
            "+-------+-----+---------------+"
        )
        result = format_table(headers, rows)
        self.assertEqual(result, expected)

    def test_format_table_empty_cell(self):
        headers = ["Col1", "Col2"]
        rows = [["", "Test"]]
        expected = (
            "+------+------+\n"
            "| Col1 | Col2 |\n"
            "+------+------+\n"
            "|      | Test |\n"
            "+------+------+"
        )
        result = format_table(headers, rows)
        self.assertEqual(result, expected)

    def test_format_table_multiline(self):
        headers = ["Description"]
        # This cell contains an explicit newline.
        rows = [["Line one.\nLine two is longer."]]
        # The header "Description" (11 characters) and the two lines from the cell:
        # "Line one." is 9 characters and "Line two is longer." is 19 characters.
        # Thus, the column width is 19.
        #
        # Note: textwrap.wrap will treat the entire string as a single paragraph,
        # so it will collapse the newline into a space and re-wrap:
        # The combined text becomes: "Line one. Line two is longer."
        # which will be wrapped into two lines:
        #   "Line one. Line two"  (18 characters)
        #   "is longer."          (10 characters)
        expected = (
            "+---------------------+\n"
            "| Description         |\n"
            "+---------------------+\n"
            "| Line one. Line two  |\n"
            "| is longer.          |\n"
            "+---------------------+"
        )
        result = format_table(headers, rows)
        self.assertEqual(result, expected)


if __name__ == "__main__":
    unittest.main()
