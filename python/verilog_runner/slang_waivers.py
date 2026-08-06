# SPDX-License-Identifier: Apache-2.0

"""Reject Slang lint waivers that can leak beyond their intended source scope."""

import re
import sys


DIRECTIVE = re.compile(r"(?://|/\*)\s*slang\s+lint_(save|off|on|restore)\b")


def check_file(path):
    errors = []
    scopes = []
    with open(path, encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            for match in DIRECTIVE.finditer(line):
                directive = match.group(1)
                if directive == "save":
                    scopes.append([line_number, False])
                elif directive == "off":
                    if not scopes:
                        errors.append(
                            "{}:{}: lint_off requires lint_save".format(
                                path, line_number
                            )
                        )
                    else:
                        scopes[-1][1] = True
                elif directive == "on":
                    errors.append(
                        "{}:{}: use lint_restore to preserve warning-as-error severity".format(
                            path, line_number
                        )
                    )
                elif not scopes:
                    errors.append(
                        "{}:{}: lint_restore has no lint_save".format(path, line_number)
                    )
                else:
                    saved_line, has_waiver = scopes.pop()
                    if not has_waiver:
                        errors.append(
                            "{}:{}: lint_save has no lint_off".format(path, saved_line)
                        )

    for saved_line, _ in scopes:
        errors.append("{}:{}: lint_save has no lint_restore".format(path, saved_line))
    return errors


def main(paths):
    errors = [error for path in paths for error in check_file(path)]
    for error in errors:
        print(error, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
