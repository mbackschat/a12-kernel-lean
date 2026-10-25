#!/usr/bin/env python3
"""Fail when .locmetryrc leaves a counted file unclaimed or keeps an entry that decides no file.

Locmetry reports an unclaimed documentation or data file nowhere but its per-file JSON, and exits 0
(measured with locmetry 0.11.1 on 2026-10-25 by dropping docs/EVIDENCE.md from the policy), so a new
file would silently fall out of the category inventory. The policy deliberately has no catch-all, so
this guard is what turns an unclassified addition into a decision. An entry that decides no file is
the opposite drift: a renamed or deleted path whose rule outlived it. Takes no input.
"""
import json
import os
import shutil
import subprocess
import sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      stdin=subprocess.DEVNULL).stdout.strip() or os.getcwd()


def main():
    if shutil.which("locmetry") is None:
        print("locmetry policy guard requires locmetry (brew install locmetry)", file=sys.stderr)
        return 1
    # User defaults may add exclusions, which would hide files from the check.
    run = subprocess.run(["locmetry", "--no-user-config", "--files", "--format", "json", "--root", ROOT],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
    if run.returncode != 0:
        print(f"locmetry exited {run.returncode}: {run.stderr.strip()}", file=sys.stderr)
        return 1
    report = json.loads(run.stdout)
    unclaimed = sorted(f["path"] for f in report["files"] if f["category"] == "unclaimed")
    unused = [e["id"] for e in report["summary"]["policy_entries"] if e["files"] == 0]
    for path in unclaimed:
        print(f"{path}: unclaimed; add a .locmetryrc rule naming its role "
              "(for a document, its lifecycle in docs/README.md)", file=sys.stderr)
    for entry in unused:
        print(f".locmetryrc: entry '{entry}' decides no file; update or delete it", file=sys.stderr)
    if unclaimed or unused:
        return 1
    print(f"locmetry policy classifies all {len(report['files'])} counted files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
