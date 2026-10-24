#!/usr/bin/env python3
"""Fail a relative link in tracked Markdown or Lean prose whose file or anchor does not exist.

Checks every tracked `*.md` and `*.lean` file and takes no input. Reading the list from stdin let a
run without a pipe block forever on an open stdin, and an empty stdin pass having checked nothing
(both observed 2026-10-24), so the file set is computed here and an empty one fails.
check-doc-hygiene.sh owns why this runs; this file owns only how.
"""
import os
import re
import subprocess
import sys
import unicodedata
import urllib.parse

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      stdin=subprocess.DEVNULL).stdout.strip() or os.getcwd()
PARENT = os.path.dirname(ROOT)
# A target outside the repository must land in one of these, since climbing one level too far is
# the defect itself; it is checked when that sibling is present and skipped where CI has none.
SIBLINGS = {"a12-kernel", "a12-rulekit", "a12-rulekit-measure"}
FENCE = re.compile(r"^```.*?^```", re.S | re.M)
INLINE_CODE = re.compile(r"`[^`\n]*`")
LINK = re.compile(r"\]\(([^)\s]+)\)")
HEADING = re.compile(r"^#{1,6}\s+(.*?)\s*$", re.M)
EXPLICIT_ANCHOR = re.compile(r'<a id="([^"]+)"')


def blank_code(text):
    """Inline code and fenced blocks quote links rather than make them; keep line numbers."""
    text = FENCE.sub(lambda match: "\n" * match.group(0).count("\n"), text)
    return INLINE_CODE.sub("", text)


def slug(heading):
    """GitHub's heading anchor: lowercase, punctuation and symbols dropped, spaces to hyphens.

    Letters, marks and digits survive, so a heading's variation selector stays in its anchor, and a
    dropped character between two spaces leaves a double hyphen rather than collapsing it."""
    out = []
    for character in heading.replace("`", "").strip().lower():
        if character == " ":
            out.append("-")
        elif character in "-_" or unicodedata.category(character)[0] not in "PS":
            out.append(character)
    return "".join(out)


_anchors = {}


def anchors(path):
    if path not in _anchors:
        text = open(path, encoding="utf-8").read()
        found = set(EXPLICIT_ANCHOR.findall(text))
        seen = {}
        for heading in HEADING.findall(FENCE.sub("", text)):
            base = slug(heading)
            count = seen.get(base, 0)
            found.add(base if count == 0 else f"{base}-{count}")
            seen[base] = count + 1
        _anchors[path] = found
    return _anchors[path]


def check(path, number, target):
    if re.match(r"(https?:|mailto:|<)", target) or re.fullmatch(r"A12Kernel\.[\w.']+", target):
        return None
    file, _, anchor = target.partition("#")
    resolved = os.path.normpath(os.path.join(ROOT, os.path.dirname(path), file)) if file else os.path.join(ROOT, path)
    if not resolved.startswith(ROOT + os.sep):
        sibling = os.path.relpath(resolved, PARENT).split(os.sep)[0]
        if sibling not in SIBLINGS:
            return f"{path}:{number}: relative link target {file} leaves the repository but names no sibling checkout"
        if os.path.isdir(os.path.join(PARENT, sibling)) and not os.path.exists(resolved):
            return f"{path}:{number}: relative link target {file} does not exist"
        return None
    if not os.path.exists(resolved):
        return f"{path}:{number}: relative link target {file} does not exist"
    if anchor and resolved.endswith(".md") and urllib.parse.unquote(anchor) not in anchors(resolved):
        return f"{path}:{number}: anchor #{anchor} does not exist in {os.path.relpath(resolved, ROOT)}"
    return None


def tracked_prose():
    listing = subprocess.run(["git", "ls-files", "-z", "--", "*.md", "*.lean"],
                             cwd=ROOT, capture_output=True, text=True, stdin=subprocess.DEVNULL)
    if listing.returncode != 0:
        sys.exit(f"relative-link check: git ls-files failed: {listing.stderr.strip()}")
    return [path for path in listing.stdout.split("\0") if path]


def main():
    os.chdir(ROOT)
    paths = tracked_prose()
    if not paths:
        print("relative-link check: no tracked Markdown or Lean file to check", file=sys.stderr)
        return 1
    broken = False
    for path in paths:
        text = blank_code(open(path, encoding="utf-8").read())
        for number, line in enumerate(text.split("\n"), 1):
            for target in LINK.findall(line):
                problem = check(path, number, target)
                if problem:
                    print(problem, file=sys.stderr)
                    broken = True
    return 1 if broken else 0


if __name__ == "__main__":
    sys.exit(main())
