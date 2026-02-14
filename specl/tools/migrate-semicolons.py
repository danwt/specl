#!/usr/bin/env python3
"""Migrate specl files from 'and' assignment separators to semicolons.

Transforms:
    x = expr           ->    x = expr;
    and y = expr             y = expr;
    and z = expr             z = expr;

Also adds semicolons after 'require' lines in action bodies.

Boolean 'and' (in invariants, guards, expressions) is NOT changed.
Comments are preserved.
"""

import re
import sys


def add_semicolon_to_line(line):
    """Add ; after the code portion of a line, before any trailing comment."""
    stripped = line.rstrip()
    # Find trailing // comment (simple heuristic — not inside a string)
    idx = stripped.find("  //")
    if idx >= 0:
        code_part = stripped[:idx].rstrip()
        comment_part = stripped[idx:]
        return code_part + ";" + comment_part
    return stripped + ";"


def migrate(content):
    lines = content.split("\n")
    result = []

    for line in lines:
        stripped = line.lstrip()
        indent = line[: len(line) - len(stripped)]

        # Skip comment lines
        if stripped.startswith("//"):
            result.append(line)
            continue

        # Pattern: line starts with "and identifier =" (not "==")
        # This is an assignment separator, not boolean AND
        m = re.match(r"and\s+(\w+\s*=(?!=).*)", stripped)
        if m:
            # Add ; to end of previous non-blank, non-comment line
            for j in range(len(result) - 1, -1, -1):
                prev = result[j].rstrip()
                if not prev or prev.lstrip().startswith("//"):
                    continue
                if not prev.endswith(";"):
                    result[j] = add_semicolon_to_line(result[j])
                break
            # Remove "and " prefix
            result.append(indent + m.group(1))
            continue

        result.append(line)

    # Second pass: add ; after require lines and last assignment before }
    final = []
    for i, line in enumerate(result):
        stripped = line.lstrip()

        # Add ; after require lines only if the expression is single-line.
        # Multi-line requires (e.g. "require all k in 0..N:\n  ...") continue
        # on the next line, so we check if the next meaningful line starts a
        # new statement (require, assignment, or closing brace).
        if stripped.startswith("require ") and not stripped.endswith(";"):
            next_meaningful = ""
            for k in range(i + 1, len(result)):
                ns = result[k].strip()
                if ns and not ns.startswith("//"):
                    next_meaningful = ns
                    break
            if (
                next_meaningful.startswith("require ")
                or next_meaningful == "}"
                or re.match(r"\w+\s*=(?!=)", next_meaningful)
            ):
                final.append(add_semicolon_to_line(line))
                continue

        # Add ; after last statement before closing brace of action/init blocks
        if stripped == "}" and final:
            for j in range(len(final) - 1, -1, -1):
                prev_stripped = final[j].strip()
                if not prev_stripped:
                    continue
                if prev_stripped.startswith("//"):
                    continue
                # If line doesn't already end with ; or { and contains
                # an assignment pattern (ident = expr, not ==)
                if (
                    not prev_stripped.endswith(";")
                    and not prev_stripped.endswith("{")
                    and prev_stripped != "}"
                    and re.search(r"\w+\s*=(?!=)", prev_stripped)
                ):
                    final[j] = add_semicolon_to_line(final[j])
                break

        final.append(line)

    return "\n".join(final)


def main():
    if len(sys.argv) < 2:
        print("Usage: migrate-semicolons.py <file.specl> [...]")
        sys.exit(1)

    changed = 0
    unchanged = 0
    for path in sys.argv[1:]:
        with open(path) as f:
            original = f.read()
        migrated = migrate(original)
        if migrated != original:
            with open(path, "w") as f:
                f.write(migrated)
            changed += 1
        else:
            unchanged += 1

    print(f"migrated: {changed}, unchanged: {unchanged}")


if __name__ == "__main__":
    main()
