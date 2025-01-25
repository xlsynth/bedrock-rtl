# find the list of files that match the given pattern */sim/chipstack/*_gen_tb.sv

import glob
import re


def find_files(directory, pattern):
    pattern = "*/sim/chipstack/*_gen_tb.sv"
    return glob.glob(pattern)


def process_line(line, max_length=50):
    """
    Process a line by splitting its string section into smaller parts if present.
    Non-string sections are returned unchanged.

    Args:
        line (str): The input line to process.
        max_length (int): The maximum length of each part of the string section.

    Returns:
        str or list: The processed line with the string section split, or the original line.
    """
    # Check if there is a string section in the line
    string_match = re.search(r'".*?"', line)
    if string_match:
        # Extract the string section
        string_section = string_match.group(0).strip('"')

        # Split the string section into smaller parts
        split_parts = split_string(string_section, max_length)

        # Replace the original string section with the split version
        split_string_lines = [f'"{part}"' for part in split_parts]

        # Preserve the rest of the line
        processed_line = re.sub(
            r'".*?"', "{" + ",\n".join(split_string_lines) + "}", line, count=1
        )
        return processed_line
    else:
        # Return the original line if no string section is found
        return line


def split_string(input_string, max_length=50):
    """
    Split a string into smaller parts, each less than max_length characters,
    preferring sentence boundaries. If not possible, split at word boundaries.

    Args:
        input_string (str): The string to split.
        max_length (int): The maximum length of each part.

    Returns:
        list: A list of split string parts.
    """
    if not input_string:
        return []

    sentences = re.split(r"(?<=[.!?])\s+", input_string)
    result = []

    for sentence in sentences:
        if len(sentence) <= max_length:
            result.append(sentence)
        else:
            words = sentence.split()
            part = ""
            for word in words:
                if len(part) + len(word) + 1 > max_length:  # +1 for space
                    result.append(part.strip())
                    part = word
                else:
                    part += " " + word
            if part:
                result.append(part.strip())

    return result


if __name__ == "__main__":
    files = find_files(".", "*/sim/chipstack/*_gen_tb.sv")

    for file in files:
        print(file)
        with open(file, "r") as f:
            lines = f.read().splitlines()
            new_lines = []
            for i, line in enumerate(lines, 1):
                new_lines.append(process_line(line, max_length=80))
            with open(f"{file}_updated.sv", "w") as f:
                f.write("\n".join(new_lines))
