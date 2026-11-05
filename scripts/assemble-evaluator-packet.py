"""Assemble an evaluator packet (U01, U02) from one committed revision of a12-kernel-lean.

Usage: python3 -I scripts/assemble-evaluator-packet.py <repo> <revision> <version> <out-dir> [<changes>]
Every file is read from the revision with `git show`, never from the working tree, except the observed
kernel's runtime artifacts: Git ignores them (docs/KERNEL-UPGRADE-PLAYBOOK.md), so each is read from the local
re-capture and must match its digest in the revision's evidence/kernel-<OBSERVED>/RECAPTURE.sha256. Requests,
models and documents are the frozen inputs under evidence/kernel-<FROZEN>/captures/ that the re-capture ran.
A request is paired with its artifact by the re-capture script's own `artifact_name`.
"""
import hashlib, importlib.util, json, os, re, subprocess, sys

# The frozen inputs' kernel and the kernel the packet's artifacts were observed on; an upgrade edits these two.
FROZEN, OBSERVED = "30.8.1", "31.1.1"

_recapture = importlib.util.spec_from_file_location(
    "recapture", os.path.join(os.path.dirname(os.path.abspath(__file__)), "recapture-kernel-evidence.py"))
recapture = importlib.util.module_from_spec(_recapture)
_recapture.loader.exec_module(recapture)

repo, rev, version, out = sys.argv[1:5]
changes = sys.argv[5] if len(sys.argv) > 5 else None
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
# The spec ends each section with provenance links into docs/sources/; shipping them keeps those links
# resolvable inside the packet (PLAN.md spec-rewrite `self-contained`).
sources = sorted(p for p in tree if re.fullmatch(r"docs/sources/[^/]+\.md", p))
for p in sources:
    put(p, show(p))
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

root = f"evidence/kernel-{FROZEN}/captures/"
packet_root = f"evidence/kernel-{OBSERVED}/captures/"
local_root = os.path.join(repo, f"evidence/kernel-{OBSERVED}/local/captures")
digests = {line[66:]: line[:64] for line in show(f"evidence/kernel-{OBSERVED}/RECAPTURE.sha256").decode().splitlines() if line}

def observed(rel):
    """The local observed-kernel artifact at rel (relative to the captures root), checked against its digest."""
    if rel not in digests:
        return None
    data = open(os.path.join(local_root, rel), "rb").read()
    if hashlib.sha256(data).hexdigest() != digests[rel]:
        sys.exit(f"{rel}: the local artifact differs from RECAPTURE.sha256; re-run the re-capture")
    return data
counts = {"requests": 0, "rows": 0, "engines-disagree": 0, "kernel-fault": 0, "host-feature": 0, "pattern": 0, "candidate": 0}
for p in sorted(t for t in tree if t.startswith(root) and t.endswith(".json")):
    base = os.path.basename(p)
    artifact_base = recapture.artifact_name(base)
    if artifact_base is None:
        continue
    artifact = os.path.join(os.path.dirname(p), artifact_base)
    artifact_data = observed(artifact[len(root):])
    if artifact_data is None:
        continue
    try:
        request = json.loads(show(p))
    except json.JSONDecodeError:
        continue
    if not isinstance(request, dict) or "rows" not in request:
        continue
    # A request names its model and documents beside it; the re-capture's `retained` resolves the few stored
    # under another name, and the packet ships each under the name the request uses.
    request_rel = p[len(root):]
    def named(name):
        return (os.path.normpath(recapture.retained(root.rstrip("/"), request_rel, name)),
                os.path.normpath(os.path.join(os.path.dirname(request_rel), name)))
    model_path, _ = named(request["model"])
    files = {(p, request_rel), named(request["model"])} | {named(r["document"]) for r in request["rows"] if "document" in r}
    missing = [source for source, _ in files if source not in tree]
    if missing:
        sys.exit(f"{p}: not in the revision: {missing}")
    for source, target in files:
        put(packet_root + target, show(source))
    # The local artifact keeps the Kernel's message text, which never leaves this repository's tree.
    put(packet_root + artifact[len(root):], re.sub(rb'("(?:message|summary)"\s*:\s*)"(?:[^"\\]|\\.)*"',
        lambda m: m.group(1) + b'"[redacted: Kernel message text, EUPL localisation resource]"', artifact_data))
    counts["requests"] += 1
    try:
        model = json.loads(show(model_path))
    except json.JSONDecodeError as e:
        sys.exit(f"{model_path}: {e}")
    rows_seen = {r["name"]: r for r in json.loads(artifact_data)["rows"]}
    host = "customConditions" in request or "customFieldTypes" in request
    bad_pattern = any(v not in TRIO for v in patterns(model))
    for row in request["rows"]:
        o = rows_seen.get(row["name"])
        if o is None:
            continue
        counts["rows"] += 1
        first = o["engines"][0]
        key = ("engines-disagree" if o.get("enginesAgree") is False else "kernel-fault" if "fault" in first
               else "host-feature" if host else "pattern" if bad_pattern else "candidate")
        counts[key] += 1

change_line = f"- Changes from the previous version: {changes}\n" if changes else ""
put("PACKET.md", f"""# Evaluator packet {version}

- Source: a12-kernel-lean revision `{full}`; every file below was read from that revision.
- Start with [the evaluator kit](docs/IMPLEMENTER-KIT-EVALUATOR.md).
{change_line}- `spec/`: {len(spec)} files, the semantics map and the numbered chapters.
- `docs/IMPLEMENTER-GUIDE.md`: the host-input contract section only.
- `docs/sources/`: {len(sources)} provenance files the spec's `Sources:` lines cite; the spec text stays normative on its own.
- `evidence/kernel-{OBSERVED}/captures/`: {counts['requests']} requests with their kernel {OBSERVED} artifacts, models and document files.

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
