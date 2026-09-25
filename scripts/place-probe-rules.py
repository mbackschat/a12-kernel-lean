#!/usr/bin/env python3
"""Place hand-written validation rules into a DM-JSON model for one `dmtool model check` run.

Why this exists, measured: `rule check` refuses an error field outside the rule group with the
instrument's own `RK_ERROR_FIELD_OUTSIDE_GROUP` before the Kernel sees the rule, so every probe of
that locus must write its rules into the model file and read the Kernel's verdict from `model
check`. Six grids on 2026-09-24 and 2026-09-25 re-typed the same placement code inline; this is that
code once. `make-probe-ops.sh` stays the route for rows `rule check` and `computation add` accept.

    ./scripts/place-probe-rules.py <model.json> <rules.txt> <out.json>

Each non-blank, non-`#` line of the rules file is `id|group path|error path|condition`: the rule is
appended to the named group's elements, and the error path is relative to the rule element, so
`../Result` from `/Fulfilment/Summary` and `../../Summary/Result` from `/Fulfilment/Ledger`. Every
rule carries the one-word English message `m`, which keeps rendered message text out of the model.
"""
import json
import sys


def find_group(node, group_id):
    if isinstance(node, dict):
        if node.get("type") == "Group" and node.get("id") == group_id:
            return node
        children = node.values()
    elif isinstance(node, list):
        children = node
    else:
        return None
    for child in children:
        found = find_group(child, group_id)
        if found is not None:
            return found
    return None


def main():
    if len(sys.argv) != 4:
        sys.exit("usage: place-probe-rules.py <model.json> <rules.txt> <out.json>")
    model_path, rules_path, out_path = sys.argv[1:]
    model = json.load(open(model_path))
    placed = 0
    for number, line in enumerate(open(rules_path), start=1):
        line = line.rstrip("\n")
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("|", 3)
        if len(fields) != 4:
            sys.exit(f"{rules_path}:{number}: expected id|group|error path|condition")
        rule_id, group_id, error_path, condition = fields
        group = find_group(model, group_id)
        if group is None:
            sys.exit(f"{rules_path}:{number}: no group {group_id}")
        group["Group"].setdefault("elements", []).append({
            "type": "Rule", "id": f"{group_id}/{rule_id}", "name": rule_id,
            "Rule": {"errorEntityRelPath": error_path, "errorCode": rule_id,
                     "errorCondition": condition, "severity": "ERROR",
                     "errorMessage": [{"locale": "en_US", "text": "m"}]}})
        placed += 1
    json.dump(model, open(out_path, "w"))
    print(f"{placed} rules placed into {out_path}")


if __name__ == "__main__":
    main()
