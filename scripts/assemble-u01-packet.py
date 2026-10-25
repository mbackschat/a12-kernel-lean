"""Assemble a U01 packet from one committed revision of a12-kernel-lean.

Usage: python3 -I scripts/assemble-u01-packet.py <repo> <revision> <version> <out-dir>
Every file is read from the revision with `git show`, never from the working tree.
"""
import hashlib, json, os, re, subprocess, sys

repo, rev, version, out = sys.argv[1:5]
if os.path.exists(out):
    sys.exit(f"{out} exists; a packet is never edited in place")

def show(path):
    # A tracked symlink shows its target text; follow it so the packet holds the content itself.
    for _ in range(8):
        entry = subprocess.run(["git", "-C", repo, "ls-tree", rev, "--", path], check=True, capture_output=True, text=True).stdout
        data = subprocess.run(["git", "-C", repo, "show", f"{rev}:{path}"], check=True, capture_output=True).stdout
        if not entry.startswith("120000 "):
            return data
        path = os.path.normpath(os.path.join(os.path.dirname(path), data.decode().strip()))
    sys.exit(f"{path}: symlink chain too long")

def put(rel, data):
    target = os.path.join(out, rel)
    os.makedirs(os.path.dirname(target), exist_ok=True)
    with open(target, "wb") as f:
        f.write(data)

full = subprocess.run(["git", "-C", repo, "rev-parse", rev], check=True, capture_output=True, text=True).stdout.strip()
tree = subprocess.run(["git", "-C", repo, "ls-tree", "-r", "--name-only", rev], check=True, capture_output=True, text=True).stdout.split("\n")

spec = sorted(p for p in tree if re.fullmatch(r"spec/(SEMANTICS-MAP|\d\d-[a-z-]+)\.md", p) and not p.startswith("spec/13-"))
for p in spec:
    put(p, show(p))
put("docs/IMPLEMENTER-KIT-EVALUATOR.md", show("docs/IMPLEMENTER-KIT-EVALUATOR.md"))
guide = show("docs/IMPLEMENTER-GUIDE.md").decode()
section = re.search(r"^## Host-input contract\n.*?(?=^## )", guide, re.S | re.M).group(0)
put("docs/IMPLEMENTER-GUIDE.md", ("# Implementer guide (packet extract)\n\nThis file holds only the host-input contract section of the implementer guide. Links leaving the packet are provenance only.\n\n" + section).encode())

TRIO = {"", "[0-9]+", "[A-Z]+"}
def patterns(x):
    if isinstance(x, dict):
        for k, v in x.items():
            if k == "pattern" and isinstance(v, str):
                yield v
            yield from patterns(v)
    elif isinstance(x, list):
        for v in x:
            yield from patterns(v)

root = "evidence/kernel-30.8.1/captures/"
counts = {"requests": 0, "rows": 0, "engines-disagree": 0, "kernel-fault": 0, "host-feature": 0, "pattern": 0, "candidate": 0}
for p in sorted(t for t in tree if t.startswith(root) and t.endswith(".json")):
    base = os.path.basename(p)
    suffix = base[len("request"):] if base.startswith("request") else base[3:] if base.startswith("req") else None
    if suffix is None:
        continue
    artifact = os.path.join(os.path.dirname(p), "artifact" + suffix)
    if artifact not in tree:
        continue
    try:
        request = json.loads(show(p))
    except json.JSONDecodeError:
        continue
    if not isinstance(request, dict) or "rows" not in request:
        continue
    directory = os.path.dirname(p)
    model_path = os.path.normpath(os.path.join(directory, request["model"]))
    files = {p, artifact, model_path} | {os.path.normpath(os.path.join(directory, r["document"])) for r in request["rows"] if "document" in r}
    missing = [f for f in files if f not in tree]
    if missing:
        sys.exit(f"{p}: not in the revision: {missing}")
    for f in files:
        put(f, show(f))
    counts["requests"] += 1
    try:
        model = json.loads(show(model_path))
    except json.JSONDecodeError as e:
        sys.exit(f"{model_path}: {e}")
    observed = {r["name"]: r for r in json.loads(show(artifact))["rows"]}
    host = "customConditions" in request or "customFieldTypes" in request
    bad_pattern = any(v not in TRIO for v in patterns(model))
    for row in request["rows"]:
        o = observed.get(row["name"])
        if o is None:
            continue
        counts["rows"] += 1
        first = o["engines"][0]
        key = ("engines-disagree" if o.get("enginesAgree") is False else "kernel-fault" if "fault" in first
               else "host-feature" if host else "pattern" if bad_pattern else "candidate")
        counts[key] += 1

put("PACKET.md", f"""# U01 evaluator packet {version}

- Source: a12-kernel-lean revision `{full}`; every file below was read from that revision.
- Start with [the evaluator kit](docs/IMPLEMENTER-KIT-EVALUATOR.md).
- `spec/`: {len(spec)} files, the semantics map and the numbered chapters.
- `docs/IMPLEMENTER-GUIDE.md`: the host-input contract section only.
- `evidence/kernel-30.8.1/captures/`: {counts['requests']} artifact-backed requests with their models and document files.

Artifact rows by the kit's classification, cases 1 to 4 and the remainder (case 5, the clock exclusion, and the evaluator's own refusals are decided by the evaluator):

| Class | Rows |
|---|---|
| all artifact rows | {counts['rows']} |
| engines disagree (excluded) | {counts['engines-disagree']} |
| Kernel fault (excluded) | {counts['kernel-fault']} |
| host feature (unsupported) | {counts['host-feature']} |
| pattern (unsupported) | {counts['pattern']} |
| remaining, in profile unless case 5 applies | {counts['candidate']} |
""".encode())

entries = []
for dirpath, _, names in os.walk(out):
    for n in names:
        full_path = os.path.join(dirpath, n)
        rel = os.path.relpath(full_path, out)
        entries.append((rel, hashlib.sha256(open(full_path, "rb").read()).hexdigest()))
manifest = "".join(f"{h}  {r}\n" for r, h in sorted(entries))
put("MANIFEST.sha256", manifest.encode())
print(json.dumps(counts), len(entries), hashlib.sha256(manifest.encode()).hexdigest())
