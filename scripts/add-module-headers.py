#!/usr/bin/env python3
"""
Ensures each Lean file in LakeJs/ has:
module

<imports>

@[expose] public section

namespace LakeJs.<Filename>

...
end LakeJs.<Filename>
"""

import os
import re
import glob

SECTION_CLOSING_FILES = {"Lookup", "TyPretty", "LeanPrimTy", "Layout", "ExternsMeta"}

def process_file(filepath):
    filename = os.path.basename(filepath)
    stem = os.path.splitext(filename)[0]
    expected_ns = f"LakeJs.{stem}"

    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    lines = content.splitlines()

    # If the file starts with a block comment before imports (e.g. FloatDecide.lean),
    # extract that comment so it can be placed after the namespace.
    leading_comment = []
    i = 0
    while i < len(lines) and lines[i].strip() == "":
        i += 1

    if i < len(lines) and lines[i].strip().startswith("/-") and lines[i].strip() != "module":
        comment_lines = []
        while i < len(lines):
            comment_lines.append(lines[i])
            if "-/" in lines[i]:
                i += 1
                break
            i += 1
        leading_comment = comment_lines

    # Skip 'module' and blank lines
    while i < len(lines) and (lines[i].strip() == "module" or lines[i].strip() == ""):
        i += 1

    # Collect import lines
    imports = []
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if (
            stripped.startswith("import ")
            or stripped.startswith("public import ")
            or stripped.startswith("meta import ")
            or stripped.startswith("public meta import ")
        ):
            if stripped.startswith("import "):
                line = line.replace("import ", "public import ", 1)
            imports.append(line)
            i += 1
        elif stripped == "" and not imports:
            i += 1
        else:
            break

    # Remainder lines
    rest_lines = lines[i:]

    # If leading_comment was found, insert it at the start of rest_lines
    if leading_comment:
        rest_lines = leading_comment + [""] + rest_lines

    # Remove existing @[expose] public section from rest_lines
    filtered = []
    for line in rest_lines:
        stripped = line.strip()
        if stripped == "@[expose] public section":
            continue
        filtered.append(line)

    # Remove existing namespace declarations matching LakeJs.<stem> or old file-level namespace
    final_body = []
    for line in filtered:
        stripped = line.strip()
        if stripped == f"namespace {expected_ns}":
            continue
        if stem == "ExternTable" and stripped == "namespace LakeJs":
            continue
        if stem == "FloatDecide" and stripped == "namespace FloatDecide":
            continue
        if stem == "FloatDecideTests" and stripped == "namespace FloatDecide.Tests":
            continue
        final_body.append(line)

    # Clean leading whitespace
    while final_body and final_body[0].strip() == "":
        final_body.pop(0)

    # Clean trailing lines
    while final_body and final_body[-1].strip() == "":
        final_body.pop()

    # Remove old trailing 'end' for removed namespaces/sections
    if final_body and final_body[-1].strip() == f"end {expected_ns}":
        final_body.pop()
    elif final_body and stem == "ExternTable" and final_body[-1].strip() == "end LakeJs":
        final_body.pop()
    elif final_body and stem == "FloatDecide" and final_body[-1].strip() == "end FloatDecide":
        final_body.pop()
    elif final_body and stem == "FloatDecideTests" and final_body[-1].strip() == "end FloatDecide.Tests":
        final_body.pop()

    while final_body and final_body[-1].strip() == "":
        final_body.pop()

    # In files where 'end' closed the old @[expose] public section, pop it
    if final_body and final_body[-1].strip() == "end" and stem in SECTION_CLOSING_FILES:
        final_body.pop()

    while final_body and final_body[-1].strip() == "":
        final_body.pop()

    # Assemble
    new_parts = ["module"]
    if imports:
        new_parts.append("")
        new_parts.extend(imports)
    new_parts.append("")
    new_parts.append("@[expose] public section")
    new_parts.append("")
    new_parts.append(f"namespace {expected_ns}")
    new_parts.append("")
    new_parts.extend(final_body)
    new_parts.append("")
    new_parts.append(f"end {expected_ns}")
    new_parts.append("")

    new_content = "\n".join(new_parts)

    with open(filepath, "w", encoding="utf-8") as f:
        f.write(new_content)
    print(f"Updated {filepath}")

def main():
    files = sorted(glob.glob("LakeJs/*.lean"))
    for f in files:
        process_file(f)

if __name__ == "__main__":
    main()
