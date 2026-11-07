#!/usr/bin/env python3
"""Re-capture the retained kernel evidence on a new kernel through the pinned measurement checkout.

The routine is docs/KERNEL-UPGRADE-PLAYBOOK.md's re-capture step. Inputs are the frozen requests, models,
documents and rule-check operations under evidence/kernel-<from>/captures/. Runtime artifacts and the
input copies the instrument needs go into evidence/kernel-<to>/local/captures/, which Git ignores; only the
rule-check observations (replayed by `lake test`) land under evidence/kernel-<to>/captures/, and `manifest`
writes evidence/kernel-<to>/RECAPTURE.sha256, the digest of every local artifact. `keep` copies the few runtime
artifacts NumberFormalProjection.lean replays into the committed root, their Kernel message text redacted.

  prepare  --from 30.8.1 --to 31.1.1 --stamp 28.4.0:29.4.0
  runtime  --to 31.1.1 --checkout ../a12-rulekit-measure [--jobs 4]
  static   --from 30.8.1 --to 31.1.1 --stamp 28.4.0:29.4.0 --checkout ../a12-rulekit-measure
  manifest --to 31.1.1
  keep     --to 31.1.1
  requests --to 31.1.1
  declarations --from 30.8.1 --to 31.1.1 --stamp 28.4.0:29.4.0 --checkout ../a12-rulekit-measure

`runtime` launches the probe JVM directly with the command line Gradle's `:adapter:kernelProbe` builds,
read once from Gradle's --info output: Gradle's per-call configuration cost about 40 s per request against
about 11 s direct (2026-11-04, kernel 31.1.1), and the two produce byte-identical artifacts. Every step
skips work already done, so an interrupted run resumes. The sibling checkouts' `git status --short` must be
unchanged across `runtime` and `static`.
"""
import argparse, concurrent.futures, hashlib, json, os, re, shutil, subprocess, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROBE_MAIN = "io.github.mbackschat.a12.dm.adapter.laws.KernelRuntimeProbe"


def root(version, *parts):
    return os.path.join(REPO, "evidence", f"kernel-{version}", *parts)


REQUEST_WORD = re.compile(r"(?:^|(?<=[-_.]))(request|req)(?=[-_.]|\.json$)")


def artifact_name(name):
    """The artifact a request writes: its name with the first `request` or `req` word replaced by `artifact`,
    as the frozen captures name them (`request-b.json`, `rel-request-24.json`, `rt-req.json`), or else, for a
    name starting `req` (`request2.json`), `artifact` and what follows its leading letters; None for any other
    file. The population replay pairs requests by the same rule. Matching only a leading word missed nine
    frozen requests (2026-11-05)."""
    if not name.endswith(".json"):
        return None
    match = REQUEST_WORD.search(name)
    if match is not None:
        return name[:match.start()] + "artifact" + name[match.end():]
    return "artifact" + re.sub(r"^[A-Za-z]*", "", name) if name.startswith("req") else None


def produced_by(artifact, version):
    """Whether an artifact names `version` as its runtime kernel: a file's existence alone once passed
    staged 30.8.1 artifacts as 31.3.1 runs (2026-11-07)."""
    try:
        producer = json.load(open(artifact, encoding="utf-8")).get("producer", {})
    except (OSError, json.JSONDecodeError, UnicodeDecodeError, AttributeError):
        return False
    return isinstance(producer, dict) and producer.get("kernel", {}).get("runtime") == version


def runtime_requests(base):
    """Every kernelProbe request under base: a JSON object naming a model and rows."""
    for dirpath, _, files in os.walk(base):
        for name in sorted(files):
            if artifact_name(name) is None:
                continue
            path = os.path.join(dirpath, name)
            try:
                request = json.load(open(path, encoding="utf-8"))
            except (json.JSONDecodeError, UnicodeDecodeError):
                continue
            if isinstance(request, dict) and "rows" in request and "model" in request:
                yield path, request


def restamp(text, stamp):
    old, new = stamp.split(":")
    return re.subn(r'("modelVersion"\s*:\s*")' + re.escape(old) + r'(")', r"\g<1>" + new + r"\g<2>", text, count=1)


def copy(source, target, stamp=None):
    """Copy source to target, restamping a model header when `stamp` is given; whether a stamp was replaced.
    Every frozen file carrying a `modelVersion` is a model, so the content decides, never the name
    (2026-11-07); any other file is copied byte for byte."""
    os.makedirs(os.path.dirname(target), exist_ok=True)
    if stamp is not None:
        try:
            text, count = restamp(open(source, encoding="utf-8").read(), stamp)
        except UnicodeDecodeError:
            count = 0
        if count == 1:
            open(target, "w", encoding="utf-8").write(text)
            return True
    shutil.copyfile(source, target)
    return stamp is None


# Four frozen requests name a model or document by the file name it had before it was retained; the
# mapping is the one docs/sources/inbound-handbacks.md#src-inbound-2026-11-03c pins by hash.
RETAINED_AS = {
    ("base-year-yearless-store/compact-request.json", "Compact_DM.json"): "base-year-yearless-store/compact-Compact_DM.json",
    ("base-year-yearless-store/compact-request.json", "d-empty.json"): "base-year-yearless-store/compact-d-empty.json",
    ("starred-operand-message-polarity/capacity-request.json", "StarPolarity_DM.json"): "starred-operand-message-polarity/witness-model.dm.json",
    ("starred-operand-message-polarity/witness-request.json", "StarPolarity_DM.json"): "starred-operand-message-polarity/witness-model.dm.json",
    ("starred-operand-message-polarity/allfilled-request.json", "StarCount_DM.json"): "starred-group-count-computation/model.dm.json",
}


def retained(source, request_rel, name):
    """The retained file a request names: `name` beside it, or the file RETAINED_AS maps it to."""
    mapped = RETAINED_AS.get((request_rel, name))
    return os.path.join(source, mapped) if mapped else os.path.join(source, os.path.dirname(request_rel), name)


def prepare(args):
    source, target = root(args.source, "captures"), root(args.to, "local", "captures")
    count = 0
    for path, request in runtime_requests(source):
        directory = os.path.dirname(path)
        rel = os.path.relpath(directory, source)
        request_name = os.path.basename(path)
        copy(path, os.path.join(target, rel, request_name))
        request_rel = os.path.relpath(path, source)
        model = retained(source, request_rel, request["model"])
        if not copy(model, os.path.join(target, rel, request["model"]), args.stamp):
            print(f"no {args.stamp.split(':')[0]} stamp: {os.path.relpath(model, source)}", file=sys.stderr)
        for row in request["rows"]:
            if "document" in row:
                copy(retained(source, request_rel, row["document"]), os.path.join(target, rel, row["document"]))
        count += 1
    print(f"prepared {count} requests under {os.path.relpath(target, REPO)}")


def sibling_state(checkout):
    return [subprocess.run(["git", "-C", c, "status", "--short"], capture_output=True, text=True).stdout
            for c in (checkout, os.path.join(os.path.dirname(checkout), "a12-rulekit"))]


def probe_command(checkout, request, artifact):
    """Run Gradle once for the first request and return (working directory, command prefix) it used."""
    result = subprocess.run(["./build.sh", ":adapter:kernelProbe", "--info", f"-Prequest={request}", f"-Pout={artifact}"],
                            cwd=checkout, capture_output=True, text=True)
    for line in result.stdout.splitlines():
        match = re.match(r"Starting process .* Working directory: (\S+) Command: (.*)$", line)
        if match and f" {PROBE_MAIN} " in match.group(2):
            words = match.group(2).split(" ")
            if words[-2:] != [request, artifact]:
                sys.exit("cannot split Gradle's probe command line; is a path written with a space?")
            return match.group(1), words[:-2]
    sys.exit("Gradle printed no probe command line:\n" + result.stdout[-2000:] + result.stderr[-2000:])


def runtime(args):
    checkout = os.path.abspath(args.checkout)
    pending = []
    for path, _ in runtime_requests(root(args.to, "local", "captures")):
        artifact = os.path.join(os.path.dirname(path), artifact_name(os.path.basename(path)))
        if not produced_by(artifact, args.to):
            pending.append((path, artifact))
    if not pending:
        print("every request has its artifact")
        return
    before = sibling_state(checkout)
    first, first_artifact = pending.pop(0)
    cwd, prefix = probe_command(checkout, first, first_artifact)
    failures = [] if os.path.exists(first_artifact) else [first]

    def one(job):
        request, artifact = job
        result = subprocess.run(prefix + [request, artifact + ".tmp"], cwd=cwd, capture_output=True, text=True)
        # A Kernel fault on a row is an observation: the probe exits non-zero but its artifact records it.
        kept = result.returncode == 0 or "KernelRuntimeProbe$FaultsObserved" in result.stderr
        if kept and os.path.exists(artifact + ".tmp"):
            os.replace(artifact + ".tmp", artifact)
            return None
        if os.path.exists(artifact + ".tmp"):
            os.remove(artifact + ".tmp")
        return request

    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for done, failed in enumerate(pool.map(one, pending), 2):
            if failed:
                failures.append(failed)
            if done % 50 == 0:
                print(f"{done}/{len(pending) + 1} requests, {len(failures)} failed", flush=True)
    if sibling_state(checkout) != before:
        sys.exit("SIBLING CHECKOUT CHANGED")
    print(f"{len(pending) + 1 - len(failures)} artifacts written; failed:")
    print("\n".join(os.path.relpath(f, REPO) for f in failures))


def requests(args):
    """Print every runtime request of the version's local re-capture, the population the replay runs, so the
    coverage report pairs requests by `artifact_name` rather than a copy of it."""
    base = root(args.to, "local", "captures")
    for path in sorted(os.path.relpath(p, REPO) for p, _ in runtime_requests(base)):
        print(path)


def registered_batches():
    """The (observations, model, operations) triples RuleCheckProjection.lean replays."""
    source = open(os.path.join(REPO, "A12Kernel/Evidence/RuleCheckProjection.lean"), encoding="utf-8").read()
    return re.findall(r'\("(captures/[^"]+)", "(captures/[^"]+)", "(captures/[^"]+)"\)', source)


def stage(old, local, rel, stamp):
    """Copy an input file into the local tree, restamping it when it is a model, unless the tree already holds
    it: `prepare` and `runtime` own what is there. Overwriting once put 71 frozen 30.8.1 artifacts and 13
    models a name test missed, unrestamped, into the 31.3.1 tree (2026-11-07)."""
    if not os.path.exists(os.path.join(local, rel)):
        copy(os.path.join(old, rel), os.path.join(local, rel), stamp)


def stage_directory(old, local, directory, stamp):
    """Stage a batch directory with its subdirectories, which hold the computation specs its operations name
    (the 31.3.1 run missed `specs/` when only the top level was staged)."""
    for name in os.listdir(os.path.join(old, directory)):
        rel = os.path.join(directory, name)
        if os.path.isdir(os.path.join(old, rel)):
            stage_directory(old, local, rel, stamp)
        else:
            stage(old, local, rel, stamp)


def materialize_inline_specs(cwd, operations):
    """Write each operation's inline `spec` to the spec file its arguments name and drop the member: dmtool
    0.15.0 refuses an operation key other than `id`, `verb` and `args`, where 0.14.0 read an inline spec."""
    path = os.path.join(cwd, operations)
    ops = json.load(open(path, encoding="utf-8"))
    if not isinstance(ops, list) or not any(isinstance(op, dict) and "spec" in op for op in ops):
        return
    for op in ops:
        if isinstance(op, dict) and "spec" in op:
            spec_file = next(a for a in op["args"] if a.endswith(".json"))
            json.dump(op.pop("spec"), open(os.path.join(cwd, spec_file), "w", encoding="utf-8"))
    json.dump(ops, open(path, "w", encoding="utf-8"), indent=1)


def fold_legacy_suppression(cwd, model_path):
    """Rewrite a computation spec's `errorCodesToSuppress` list as the `additionalParserInformation` preamble the
    Kernel folds it into (a12-dmkits KF298): dmtool 0.15.0 refuses the list key in a spec, so the folded text
    hands the Kernel the same computation."""
    model = json.load(open(model_path, encoding="utf-8"))
    language = model.get("content", {}).get("modelConfig", {}).get("conditionLanguage", {}).get("code", "en_US")
    keyword = "@UnterdrueckeWarnung" if language.startswith("de") else "@SuppressWarning"
    for directory, _, names in os.walk(cwd):
        for name in names:
            if not name.endswith(".json"):
                continue
            path = os.path.join(directory, name)
            try:
                spec = json.load(open(path, encoding="utf-8"))
            except ValueError:
                continue
            if isinstance(spec, dict) and "computedField" in spec and "errorCodesToSuppress" in spec:
                codes = spec.pop("errorCodesToSuppress")
                if codes and "additionalParserInformation" not in spec:
                    spec["additionalParserInformation"] = f"{keyword}({','.join(codes)})"
                json.dump(spec, open(path, "w", encoding="utf-8"), indent=2)


def envelope(dmtool, cwd, arguments):
    return json.loads(subprocess.run([dmtool] + arguments, cwd=cwd, capture_output=True, text=True).stdout)


def kernel_codes(result):
    """The Kernel's codes of one result, nested apply results included; the text is never kept."""
    diagnostics = result.get("diagnostics", []) + [d for r in result.get("data", {}).get("results", [])
                                                   if isinstance(r, dict) for d in r.get("diagnostics", [])]
    return [d["code"] for d in diagnostics if d.get("source") == "KERNEL" and d.get("code")]


def static(args):
    """Re-run every registered rule-check batch by the route its retained file shows: `batch --observations`
    for an operation list, the envelope's codes for a dry-run code table, generated `rule check` operations
    for self-contained message rows, and `apply --dry-run` for structured cases."""
    old, local, kept = root(args.source), root(args.to, "local"), root(args.to)
    checkout = os.path.abspath(args.checkout)
    dmtool = os.path.join(checkout, "cli/build/install/dmtool/bin/dmtool")
    revision = subprocess.run(["git", "-C", checkout, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    before = sibling_state(checkout)
    tables, failed = {}, []
    # The batch envelope names no version since dmtool 0.15.0; the launcher's first line does.
    launcher_version = subprocess.run([dmtool, "--version"], capture_output=True, text=True).stdout.split()[1]
    for observations, model, operations in registered_batches():
        target = os.path.join(kept, observations)
        if os.path.exists(target) and observations not in tables:
            continue
        batch = os.path.dirname(observations)
        cwd = os.path.join(local, batch)
        stage_directory(old, local, batch, args.stamp)
        stage(old, local, model, args.stamp)
        model_arg = os.path.relpath(os.path.join(local, model), cwd)
        frozen = json.load(open(os.path.join(old, observations), encoding="utf-8"))
        if isinstance(frozen, dict) and "rows" in frozen:
            env = envelope(dmtool, cwd, ["-m", model_arg, "batch", os.path.basename(operations)])
            rows = tables.setdefault(observations, {})
            for result in env["data"]["results"]:
                r = result.get("result", {})
                codes = [d for d in r.get("diagnostics", []) if d.get("code")]
                # dmtool 0.15.0 answers a rule check `ok` with the Kernel's verdict in `valid`; 0.14.0 had only `ok`.
                rows[result["id"]] = {"admitted": r.get("valid", r.get("ok")) is True,
                                      "codes": sorted({d["code"] for d in codes if d.get("source") == "KERNEL"}),
                                      "instrument": sorted({d["code"] for d in codes if d.get("source") != "KERNEL"})}
            dump_json({"kernel": args.to, "verb": frozen.get("verb"), "producer": {"revision": revision, "state": "CLEAN"},
                       "dmtool": env.get("dmtool", launcher_version), "rows": rows}, target)
        elif operations != observations:
            # The staged directory holds the frozen observations too; a stale copy must not pass as a run.
            if os.path.exists(os.path.join(local, observations)):
                os.remove(os.path.join(local, observations))
            materialize_inline_specs(cwd, os.path.basename(operations))
            fold_legacy_suppression(cwd, os.path.join(local, model))
            subprocess.run([dmtool, "-m", model_arg, "batch", os.path.basename(operations),
                            "--observations=" + os.path.basename(observations)], cwd=cwd, capture_output=True, text=True)
            produced = os.path.join(local, observations)
            if os.path.exists(produced):
                copy(produced, target)
            else:
                failed.append(observations)
        else:
            rows = frozen if isinstance(frozen, list) else frozen["observations"]
            if rows and "case" in rows[0]:
                for row in rows:
                    env = envelope(dmtool, cwd, ["-m", model_arg, "apply", row["case"] + "-spec.json", "--dry-run"])
                    row["admitted"], row["codes"] = env.get("ok") is True, kernel_codes(env)
            else:
                verdicts = {}
                for row_model in sorted({row.get("model", "") for row in rows}):
                    named = os.path.normpath(os.path.join(batch, row_model)) if row_model else model
                    if row_model and not os.path.exists(os.path.join(old, named)):
                        named = os.path.normpath(os.path.join(os.path.dirname(model), row_model))
                    stage(old, local, named, args.stamp)
                    ops = [{"id": r["id"], "verb": "rule", "args": ["check", "--code", r["id"], "--field", r["field"],
                            "--group", r["group"], "--condition", r["condition"], "--message=en_US=" + r["message"]]}
                           for r in rows if r.get("model", "") == row_model]
                    json.dump(ops, open(os.path.join(cwd, "recapture-ops.json"), "w"))
                    if os.path.exists(os.path.join(cwd, "recapture-obs.json")):
                        os.remove(os.path.join(cwd, "recapture-obs.json"))
                    subprocess.run([dmtool, "-m", os.path.relpath(os.path.join(local, named), cwd), "batch",
                                    "recapture-ops.json", "--observations=recapture-obs.json"], cwd=cwd, capture_output=True, text=True)
                    for o in json.load(open(os.path.join(cwd, "recapture-obs.json")))["observations"]:
                        verdicts[o["id"]] = o
                for row in rows:
                    row["valid"], row["codes"] = verdicts[row["id"]]["valid"], verdicts[row["id"]]["codes"]
                    if "engineVersion" in row:
                        row["engineVersion"] = args.to
                if isinstance(frozen, dict):
                    frozen["producer"] = {"source": {"revision": revision}}
            dump_json(frozen, target)
    if sibling_state(checkout) != before:
        sys.exit("SIBLING CHECKOUT CHANGED")
    print("no observations written:\n" + "\n".join(failed))


DECLARATIONS = "captures/field-declaration-notifications-2026-10-13"
RAW = "@@RAW-NUMBER@@"


def declarations(args):
    """Re-run the patch-built declaration capture through `model check`. A codeless notification carries
    only Kernel text, which is never kept: each is classed by the frozen label it pairs with, one to one at
    the same element of the same row, and a sentence no row pairs is reported for a decision by hand."""
    old, local, kept = root(args.source, DECLARATIONS), root(args.to, "local", DECLARATIONS), root(args.to, DECLARATIONS)
    checkout = os.path.abspath(args.checkout)
    dmtool = os.path.join(checkout, "cli/build/install/dmtool/bin/dmtool")
    # Number tokens stay as written: a float round-trip would turn 1.00000000000000001 into 1.0.
    load = lambda path: json.load(open(path, encoding="utf-8"), parse_float=lambda x: RAW + x + RAW)
    def dump(value, path):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        text = json.dumps(value, indent=1, ensure_ascii=True)
        open(path, "w", encoding="utf-8").write(re.sub('"' + RAW + '([^"]*)' + RAW + '"', r"\1", text))
    base = load(os.path.join(old, "Wh_DM.json"))
    base["header"]["modelVersion"] = args.stamp.split(":")[1]
    ops = []
    for row in load(os.path.join(old, "rows.json")):
        model, patch = json.loads(json.dumps(base)), row["patch"]
        groups = model["content"]["modelRoot"]["rootGroups"]
        groups[0]["Group"]["elements"] = groups[0]["Group"].get("elements", []) + patch.get("append", [])
        groups.extend(patch.get("roots", []))
        if "locales" in patch:
            model["header"]["locales"] = [{"code": code} for code in patch["locales"]]
        if "typeDefinitions" in patch:
            model["content"]["typeDefinitions"] = patch["typeDefinitions"]
        if "language" in patch:
            model["content"]["modelConfig"]["conditionLanguage"] = {"code": patch["language"]}
        dump(model, os.path.join(local, "models", row["id"] + "_DM.json"))
        ops.append({"id": row["id"], "verb": "model", "args": ["check", "-m", "models/" + row["id"] + "_DM.json"]})
    dump(base, os.path.join(local, "base_DM.json"))
    json.dump(ops, open(os.path.join(local, "ops.json"), "w"))
    before = sibling_state(checkout)
    results = envelope(dmtool, local, ["-m", "base_DM.json", "batch", "ops.json"])["data"]["results"]
    if sibling_state(checkout) != before:
        sys.exit("SIBLING CHECKOUT CHANGED")
    frozen = {o["case"]: o for o in json.load(open(os.path.join(old, "observations.json"), encoding="utf-8"))}
    element = lambda text: (re.search(r"with (?:path|id) '([^']*)'", text) or [None, None])[1]
    # Quoted names and values vary by row; a bound written in the sentence is part of its class.
    shape = lambda text: re.sub(r"'[^']*'", "#", text)
    built = "could not build this model"
    votes = {}
    for result in results:
        r = result["result"]
        for at in {element(d.get("summary", "")) for d in r.get("diagnostics", []) if not d.get("code")}:
            mine = [shape(d["summary"]) for d in r.get("diagnostics", []) if not d.get("code") and element(d["summary"]) == at]
            theirs = [n["code"] for n in frozen.get(result["id"], {}).get("notifications", [])
                      if n["code"].startswith("codeless:") and n.get("at") == at]
            if len(mine) == 1 and len(theirs) == 1:
                votes.setdefault(mine[0], set()).add(theirs[0])
    # A second pass pairs what is left at an element once the sentences the first pass classed are removed.
    for result in results:
        r = result["result"]
        for at in {element(d.get("summary", "")) for d in r.get("diagnostics", []) if not d.get("code")}:
            mine = [shape(d["summary"]) for d in r.get("diagnostics", []) if not d.get("code") and element(d["summary"]) == at]
            theirs = [n["code"] for n in frozen.get(result["id"], {}).get("notifications", [])
                      if n["code"].startswith("codeless:") and n.get("at") == at]
            for sentence in [m for m in mine if len(votes.get(m, ())) == 1]:
                label = next(iter(votes[sentence]))
                if label in theirs:
                    theirs.remove(label)
                    mine.remove(sentence)
            if len(mine) == 1 and len(theirs) == 1 and mine[0] not in votes:
                votes[mine[0]] = {theirs[0]}
    observations, unpaired = [], set()
    for result in results:
        r = result["result"]
        if r.get("verification") != "KERNEL_CONFIRMED":
            observations.append({"case": result["id"], "admitted": None, "verification": None,
                                 "notifications": [{"code": d.get("code"), "at": None} for d in r.get("diagnostics", [])]})
            continue
        notes = []
        for d in r.get("diagnostics", []):
            text = d.get("summary", "")
            if d.get("code"):
                notes.append({"code": d["code"], "at": element(text)})
            elif built in text:
                notes.append({"code": "codeless:model-not-built", "at": None})
            else:
                labels = votes.get(shape(text), set())
                if len(labels) != 1:
                    unpaired.add(result["id"])
                notes.append({"code": next(iter(labels)) if len(labels) == 1 else "codeless:unpaired", "at": element(text)})
        observations.append({"case": result["id"], "admitted": r.get("valid"), "verification": r.get("verification"),
                             "notifications": notes})
    dump_json(observations, os.path.join(kept, "observations.json"))
    print("rows with an unpaired codeless sentence, to class by hand:", sorted(unpaired))


def dump_json(value, path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w", encoding="utf-8").write(json.dumps(value, indent=1, ensure_ascii=True) + "\n")


def manifest(args):
    """Digest every request's artifact, paired by `artifact_name`: a leading-`artifact` filter left out the
    prefixed artifacts such as `rel-artifact-24.json` (2026-11-05)."""
    base = root(args.to, "local", "captures")
    lines, foreign = [], []
    for request, _ in runtime_requests(base):
        path = os.path.join(os.path.dirname(request), artifact_name(os.path.basename(request)))
        if os.path.exists(path):
            if not produced_by(path, args.to):
                foreign.append(os.path.relpath(path, base))
                continue
            digest = hashlib.sha256(open(path, "rb").read()).hexdigest()
            lines.append(f"{digest}  {os.path.relpath(path, base)}")
    if foreign:
        sys.exit(f"{len(foreign)} artifacts were not produced by kernel {args.to}; re-run `runtime`:\n" + "\n".join(foreign))
    target = root(args.to, "RECAPTURE.sha256")
    open(target, "w", encoding="utf-8").write("\n".join(sorted(lines, key=lambda l: l[66:])) + "\n")
    print(f"{len(lines)} artifacts in {os.path.relpath(target, REPO)}")


REDACTED = '"[redacted: Kernel message text, EUPL localisation resource]"'


def redact(text):
    """Kernel catalog sentences never enter the repository (CLAUDE.md's clean-room rule): each `message`
    and `summary` value is replaced in place, textually, so every other byte is unchanged."""
    return re.sub(r'("(?:message|summary)"\s*:\s*)"(?:[^"\\]|\\.)*"', lambda m: m.group(1) + REDACTED, text)


def keep(args):
    source = open(os.path.join(REPO, "A12Kernel/Evidence/NumberFormalProjection.lean"), encoding="utf-8").read()
    for _, artifact in re.findall(r'\("(captures/[^"]+)", "(captures/[^"]+)"\)', source):
        text = open(root(args.to, "local", artifact), encoding="utf-8").read()
        target = root(args.to, artifact)
        os.makedirs(os.path.dirname(target), exist_ok=True)
        open(target, "w", encoding="utf-8").write(redact(text))
        print(os.path.relpath(target, REPO))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    steps = parser.add_subparsers(dest="step", required=True)
    for name, function in (("prepare", prepare), ("runtime", runtime), ("static", static), ("manifest", manifest), ("keep", keep),
                           ("declarations", declarations), ("requests", requests)):
        step = steps.add_parser(name)
        step.set_defaults(function=function)
        step.add_argument("--to", required=True)
        if name in ("prepare", "static", "declarations"):
            step.add_argument("--from", dest="source", required=True)
            step.add_argument("--stamp", required=True, help="old:new modelVersion, as the new kernel's migrator changes it")
        if name in ("runtime", "static", "declarations"):
            step.add_argument("--checkout", required=True, help="the measurement checkout, launcher installed")
        if name == "runtime":
            step.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    args.function(args)


if __name__ == "__main__":
    main()
