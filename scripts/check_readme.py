#!/usr/bin/env python3
"""Fail unless the Lean example of README.md is, line for line, in the test file that CI compiles."""
import re
import sys

readme = open("README.md", encoding="utf-8").read()
test = open("VariationalAnalysisTest/Readme.lean", encoding="utf-8").read()

blocks = re.findall(r"```lean\n(.*?)```", readme, flags=re.S)
if not blocks:
    sys.exit("README.md has no ```lean block")

# The file has a header and a module docstring between the import and the rest.
for block in blocks:
    for part in re.split(r"\n\s*\n", block.strip()):
        if part.strip() not in test:
            sys.exit(
                "This part of the README example is not in VariationalAnalysisTest/Readme.lean:\n\n"
                + part
            )
print(f"README example: {len(blocks)} block(s) found in VariationalAnalysisTest/Readme.lean")
