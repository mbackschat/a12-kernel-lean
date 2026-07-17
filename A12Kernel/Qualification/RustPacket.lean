import A12Kernel.Process.Sha256
import A12Kernel.Qualification.MutationResult
import A12Kernel.Qualification.Packet

/-! # Frozen Rust mutation packet assembly

This IO-only module exports the exact source tree, observer, mutations, expectations, and command
policy for the post-cold Rust qualification experiment. It reads the sibling Git object database
without checking out or modifying that repository and writes only to an explicit new packet root.
-/

namespace A12Kernel.Qualification.RustPacket

open Lean
open A12Kernel.Evidence.FlatProtocolBridge
open A12Kernel.Process.Artifact
open A12Kernel.Qualification.Packet

private structure Edit where
  before : String
  after : String

private structure MutationSource where
  descriptor : MutationDescriptor
  edits : List Edit

structure MutationProjection where
  descriptor : MutationDescriptor
  mutatedLibrary : String
  patch : String

private def numberEmptyBefore := r#"        (FieldKind::Number { .. }, CheckedRead::Empty) => ComparisonOperand::Value {
            actual: ScalarValue::NumberZero,
            given: false,
        },"#

private def numberEmptyAfter :=
  "        (FieldKind::Number { .. }, CheckedRead::Empty) => ComparisonOperand::NotEvaluated,"

private def confirmEmptyBefore := r#"        (FieldKind::Confirm, CheckedRead::Empty) => ComparisonOperand::Value {
            actual: ScalarValue::Confirm(false),
            given: false,
        },"#

private def confirmEmptyAfter :=
  "        (FieldKind::Confirm, CheckedRead::Empty) => ComparisonOperand::NotEvaluated,"

private def rowGateBefore := r#"fn evaluate_full(
    has_content: bool,
    condition: &CheckedCondition,
    context: &CheckedContext,
) -> Verdict {
    if !has_content && !can_fire_on_empty(condition) {"#

private def rowGateAfter := r#"fn evaluate_full(
    _has_content: bool,
    condition: &CheckedCondition,
    context: &CheckedContext,
) -> Verdict {
    if context.cells.is_empty() && !can_fire_on_empty(condition) {"#

private def malformedBefore :=
  "        ComparisonOperand::Unknown(_) => return Verdict::Unknown,"

private def malformedAfter :=
  "        ComparisonOperand::Unknown(_) => return Verdict::NotFired,"

private def andHeaderBefore := r#"fn verdict_and(left: Verdict, right: Verdict) -> Verdict {
    match (left, right) {"#

private def andPoisonAfter := r#"fn verdict_and(left: Verdict, right: Verdict) -> Verdict {
    if left == Verdict::Unknown || right == Verdict::Unknown {
        return Verdict::Unknown;
    }
    match (left, right) {"#

private def orHeaderBefore := r#"fn verdict_or(left: Verdict, right: Verdict) -> Verdict {
    match (left, right) {"#

private def orPoisonAfter := r#"fn verdict_or(left: Verdict, right: Verdict) -> Verdict {
    if left == Verdict::Unknown || right == Verdict::Unknown {
        return Verdict::Unknown;
    }
    match (left, right) {"#

private def unknownAsFalsePrelude := r#"    let left = match left {
        Verdict::Unknown => Verdict::NotFired,
        verdict => verdict,
    };
    let right = match right {
        Verdict::Unknown => Verdict::NotFired,
        verdict => verdict,
    };
"#

private def andFalseAfter :=
  "fn verdict_and(left: Verdict, right: Verdict) -> Verdict {\n" ++
    unknownAsFalsePrelude ++ "    match (left, right) {"

private def orFalseAfter :=
  "fn verdict_or(left: Verdict, right: Verdict) -> Verdict {\n" ++
    unknownAsFalsePrelude ++ "    match (left, right) {"

private def comparisonOmissionBefore :=
  "        (true, false) => Verdict::Fired(Polarity::Omission),"

private def comparisonOmissionAfter :=
  "        (true, false) => Verdict::Fired(Polarity::Value),"

private def presenceOmissionBefore :=
  "        CheckedRead::Empty => Verdict::Fired(Polarity::Omission),"

private def presenceOmissionAfter :=
  "        CheckedRead::Empty => Verdict::Fired(Polarity::Value),"

private def mutationSources : Except String (List MutationSource) := do
  let descriptors := mutationPlan.mutations
  let sourceEdits : List (List Edit) := [
    [{ before := numberEmptyBefore, after := numberEmptyAfter }],
    [{ before := rowGateBefore, after := rowGateAfter }],
    [{ before := confirmEmptyBefore, after := confirmEmptyAfter }],
    [{ before := malformedBefore, after := malformedAfter }],
    [{ before := andHeaderBefore, after := andPoisonAfter },
      { before := orHeaderBefore, after := orPoisonAfter }],
    [{ before := andHeaderBefore, after := andFalseAfter },
      { before := orHeaderBefore, after := orFalseAfter }],
    [{ before := comparisonOmissionBefore, after := comparisonOmissionAfter },
      { before := presenceOmissionBefore, after := presenceOmissionAfter }]]
  if descriptors.length != sourceEdits.length then
    throw "Rust packet mutation source count differs from the typed mutation plan"
  pure <| descriptors.zip sourceEdits |>.map fun (descriptor, edits) => { descriptor, edits }

private def replaceOnce (input : String) (edit : Edit) (context : String) : Except String String := do
  if edit.before.isEmpty then throw s!"{context}: replacement source must not be empty"
  match input.splitOn edit.before with
  | [head, tail] => pure (head ++ edit.after ++ tail)
  | [] => throw s!"{context}: internal split failure"
  | [_] => throw s!"{context}: replacement source was not found"
  | _ => throw s!"{context}: replacement source is not unique"

private def applyEdits (input : String) (mutation : MutationSource) : Except String String :=
  mutation.edits.foldlM (fun current edit =>
    replaceOnce current edit s!"mutation {mutation.descriptor.mechanism.tag}") input

private def fileLines (input : String) : Except String (List String) := do
  if !input.endsWith "\n" then throw "qualification source asset must end in a newline"
  pure (input.dropEnd 1 |>.toString |>.splitOn "\n")

private def commonPrefixLength : List String → List String → Nat
  | left :: leftRest, right :: rightRest =>
      if left == right then commonPrefixLength leftRest rightRest + 1 else 0
  | _, _ => 0

private def prefixedLines (marker : String) (lines : List String) : String :=
  String.intercalate "\n" (lines.map (marker ++ ·)) ++ "\n"

private def changedFilePatch (path : String) (before after : String) : Except String String := do
  let beforeLines ← fileLines before
  let afterLines ← fileLines after
  let prefixCount := commonPrefixLength beforeLines afterLines
  let remainingBefore := beforeLines.drop prefixCount
  let remainingAfter := afterLines.drop prefixCount
  let suffixCount := commonPrefixLength remainingBefore.reverse remainingAfter.reverse
  let contextBefore := min prefixCount 3
  let contextAfter := min suffixCount 3
  let oldChangedCount := remainingBefore.length - suffixCount
  let newChangedCount := remainingAfter.length - suffixCount
  if oldChangedCount == 0 && newChangedCount == 0 then
    throw s!"qualification mutation did not change '{path}'"
  let start := prefixCount - contextBefore
  let leading := beforeLines.drop start |>.take contextBefore
  let removed := beforeLines.drop prefixCount |>.take oldChangedCount
  let added := afterLines.drop prefixCount |>.take newChangedCount
  let trailing := beforeLines.drop (beforeLines.length - suffixCount) |>.take contextAfter
  let oldCount := contextBefore + oldChangedCount + contextAfter
  let newCount := contextBefore + newChangedCount + contextAfter
  pure <| s!"diff --git a/{path} b/{path}\n--- a/{path}\n+++ b/{path}\n@@ -{start + 1},{oldCount} +{start + 1},{newCount} @@\n" ++
    prefixedLines " " leading ++ prefixedLines "-" removed ++
    prefixedLines "+" added ++ prefixedLines " " trailing

private def newFilePatch (path content : String) : Except String String := do
  let lines ← fileLines content
  pure <| s!"diff --git a/{path} b/{path}\nnew file mode 100644\n--- /dev/null\n+++ b/{path}\n@@ -0,0 +1,{lines.length} @@\n" ++
    prefixedLines "+" lines

private def combinedPatch (baseline mutated observer : String) : Except String String := do
  let sourcePatch ← changedFilePatch "src/lib.rs" baseline mutated
  let observerPatch ← newFilePatch observerCandidatePathText observer
  pure (sourcePatch ++ observerPatch)

private def observerOnlyPatch (observer : String) : Except String String :=
  newFilePatch observerCandidatePathText observer

/-- Reconstruct the source-owned observer-only patch from the tracked observer bytes. -/
def sourceOwnedObserverPatch (observer : String) : Except String String :=
  observerOnlyPatch observer

/-- Reconstruct every reviewed semantic patch and mutated library from the frozen natural library and tracked observer. -/
def sourceOwnedMutationProjections (baseline observer : String) :
    Except String (List MutationProjection) := do
  let sources ← mutationSources
  sources.mapM fun source => do
    let mutatedLibrary ← applyEdits baseline source
    pure {
      descriptor := source.descriptor
      mutatedLibrary
      patch := ← combinedPatch baseline mutatedLibrary observer }

private def digest (value : String) (context : String) : Except String Digest :=
  match Digest.parse value with
  | .ok digest => pure digest
  | .error error => throw s!"{context}: {error}"

private def portablePath (value : String) (context : String) : Except String PortablePath :=
  match PortablePath.parse value with
  | .ok path => pure path
  | .error error => throw s!"{context}: {error}"

private def hashFile (path : System.FilePath) : IO Digest := do
  let value ← A12Kernel.Process.Sha256.file path
  IO.ofExcept (digest value path.toString)

private def writeFile (root : System.FilePath) (relative : PortablePath)
    (content : String) (executable := false) : IO FileDigest := do
  let path := root / relative.toString
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path content
  if executable then
    IO.setAccessRights path {
      user := { read := true, write := true, execution := true }
      group := { read := true, execution := true }
      other := { read := true, execution := true } }
  pure { path := relative, sha256 := ← hashFile path }

private def processOutput (cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO String := do
  let output ← IO.Process.output { cmd, args, cwd, env }
  if output.exitCode != 0 then
    throw (IO.userError
      s!"command '{cmd}' failed with exit {output.exitCode}: {output.stderr.trimAscii.toString}")
  if !output.stderr.isEmpty then
    throw (IO.userError s!"command '{cmd}' wrote stderr: {output.stderr.trimAscii.toString}")
  pure output.stdout

private structure GitEntry where
  mode : String
  path : PortablePath

private def isBuildInput (path : PortablePath) : Bool :=
  let value := path.toString
  value == "Cargo.toml" || value == "Cargo.lock" || value == "rust-toolchain.toml" ||
    value == "build.rs" || value == "rustfmt.toml" || value == ".rustfmt.toml" ||
    value == "clippy.toml" || value == ".clippy.toml" || value.startsWith ".cargo/" ||
    value.startsWith "src/" || value.startsWith "tests/" || value.startsWith "scripts/" ||
    value.startsWith "benches/" || value.startsWith "examples/" ||
    value.startsWith "handover/"

private def isKnownNonBuildInput (path : PortablePath) : Bool :=
  let value := path.toString
  [".gitignore", "AGENTS.md", "CLAUDE.md", "LICENSE", "README.md"].contains value ||
    value.startsWith "prompts/" || value.startsWith "reports/" ||
    value.startsWith "qualification/"

private def parseGitEntry (line : String) : Except String GitEntry := do
  let (metadata, pathText) ← match line.splitOn "\t" with
    | [metadata, pathText] => pure (metadata, pathText)
    | _ => throw s!"invalid git ls-tree row: {repr line}"
  let fields := metadata.splitOn " " |>.filter (!·.isEmpty)
  let mode ← match fields with
    | [mode, "blob", _object] => pure mode
    | _ => throw s!"unsupported git ls-tree row: {repr line}"
  if mode != "100644" && mode != "100755" && mode != "120000" then
    throw s!"unsupported candidate Git mode '{mode}' for '{pathText}'"
  pure {
    mode
    path := ← portablePath pathText s!"candidate Git path '{pathText}'" }

private def gitEntriesAt (candidateRoot : System.FilePath) (revision : String) :
    IO (List GitEntry) := do
  let output ← processOutput "git"
    #["-C", candidateRoot.toString, "ls-tree", "-r", "--full-tree",
      revision]
  let allEntries ← output.trimAscii.toString.splitOn "\n" |>.filter (!·.isEmpty) |>.mapM
    fun line => IO.ofExcept (parseGitEntry line)
  for entry in allEntries do
    if !isBuildInput entry.path && !isKnownNonBuildInput entry.path then
      throw (IO.userError
        s!"candidate revision contains unclassified tracked path '{entry.path}'")
  let entries := allEntries.filter fun entry => isBuildInput entry.path
  if entries.isEmpty then throw (IO.userError "frozen candidate revision has no tracked files")
  for entry in entries do
    if entry.mode == "120000" then
      throw (IO.userError
        s!"candidate build-input closure contains unsupported symlink '{entry.path}'")
  let paths := entries.map (·.path)
  IO.ofExcept (validatePathSet paths)
  if paths.map (·.toString) != (paths.map (·.toString)).mergeSort then
    throw (IO.userError "git ls-tree did not return lexical candidate paths")
  pure entries

private def exportBaselineFile (candidateRoot packetRoot : System.FilePath)
    (entry : GitEntry) : IO SourceFile := do
  let content ← processOutput "git"
    #["-C", candidateRoot.toString, "show",
      s!"{baselineImplementationRevision}:{entry.path.toString}"]
  let packetPath ← portablePath s!"baseline/{entry.path}" "baseline packet path" |> IO.ofExcept
  let written ← writeFile packetRoot packetPath content (entry.mode == "100755")
  pure {
    candidatePath := entry.path
    packetPath
    sha256 := written.sha256
    executable := entry.mode == "100755" }

def toolchainPath : String :=
  String.intercalate ":" toolchainPathEntries

private def toolVersion (candidateRoot : System.FilePath) (name : String) : IO ToolchainSpec := do
  let args := if name == "rustc" then #["-vV"] else #["--version"]
  let output ← processOutput name args (some candidateRoot)
    #[("PATH", some toolchainPath)]
  let version := output.trimAscii.toString
  if version.isEmpty then throw (IO.userError s!"{name} returned an empty version")
  pure { name, version }

def inventoryPaths (files : List FileDigest) : String :=
  String.intercalate "\n" (files.map (·.path.toString)) ++ "\n"

def inventoryDigests (files : List FileDigest) : String :=
  String.intercalate "\n" (files.map fun file => s!"{file.sha256}  {file.path}") ++ "\n"

private def sortedFiles (files : List FileDigest) : List FileDigest :=
  files.mergeSort fun left right => left.path.toString ≤ right.path.toString

private def replaceSourceDigest (baseline : List FileDigest) (path : PortablePath)
    (sha256 : Digest) : Except String (List FileDigest) := do
  let matching := baseline.filter (·.path == path)
  if matching.length != 1 then
    throw s!"baseline source inventory does not contain exactly one '{path}'"
  pure <| baseline.map fun file => if file.path == path then { file with sha256 } else file

private def observationJson (mutation : MutationDescriptor) : Json :=
  ({
    exercise := mutation.mechanism.exercise
    caseResults := MutationResult.expectedMutationCaseResults mutation
    algebraResults := MutationResult.expectedMutationAlgebraResults mutation
  } : MutationResult.Observation).asJson

private def baselineCaseResults : List MutationResult.CaseResult :=
  capability.cases.map fun descriptor => {
    caseId := descriptor.id
    verdict := descriptor.expectedVerdict }

private def baselineAlgebraResults : List MutationResult.AlgebraResult :=
  VerdictAlgebraMutation.domain.map fun input => {
    connective := input.connective
    left := input.left
    right := input.right
    verdict := input.connective.evaluate input.left input.right }

def expectedBaselineObservationJson : Json :=
  ({
    exercise := 0
    caseResults := baselineCaseResults
    algebraResults := baselineAlgebraResults
  } : MutationResult.Observation).asJson

private def command (id : String) (argv : List String) : CommandSpec := {
  id, argv, expectedExitStatus := 0 }

private def inventoryCommand (id inventoryStem : String) : CommandSpec :=
  command id ["sh", "../packet/tools/check-inventory.sh",
    s!"../packet/expected/{inventoryStem}.paths",
    s!"../packet/expected/{inventoryStem}.sha256"]

def expectedNaturalCommands : List CommandSpec := [
  inventoryCommand "natural-source-inventory" "baseline",
  command "observer-patch-check"
    ["git", "apply", "--check", "../packet/patches/00-observer.patch"],
  command "observer-patch-apply"
    ["git", "apply", "--whitespace=nowarn", "../packet/patches/00-observer.patch"],
  inventoryCommand "instrumented-source-inventory" "instrumented-baseline",
  command "rustc-version" ["rustc", "-vV"],
  command "cargo-version" ["cargo", "--version"],
  command "observe-baseline" ["cargo", "run", "--quiet", "--bin",
    "qualification-observer", "--", "--exercise", "0"],
  command "observer-reverse-patch-check"
    ["git", "apply", "--reverse", "--check", "../packet/patches/00-observer.patch"],
  command "observer-reverse-patch"
    ["git", "apply", "--reverse", "--whitespace=nowarn",
      "../packet/patches/00-observer.patch"],
  command "natural-verify" ["sh", "scripts/verify.sh"],
  inventoryCommand "natural-restored-source-inventory" "baseline"]

def expectedFinalCommands : List CommandSpec := [
  command "final-verify" ["sh", "scripts/verify.sh"],
  inventoryCommand "final-source-inventory" "baseline"]

def expectedMutationCommands (mutation : MutationDescriptor) : List CommandSpec :=
  let stem := mutationFileStem mutation
  let patch := s!"../packet/patches/{stem}.patch"
  let exercise := toString mutation.mechanism.exercise
  [
    command "patch-check" ["git", "apply", "--check", patch],
    command "patch-apply" ["git", "apply", "--whitespace=nowarn", patch],
    inventoryCommand "mutated-source-inventory" stem,
    command "observe" ["cargo", "run", "--quiet", "--bin", "qualification-observer",
      "--", "--exercise", exercise],
    command "reverse-patch-check" ["git", "apply", "--reverse", "--check", patch],
    command "reverse-patch" ["git", "apply", "--reverse", "--whitespace=nowarn", patch],
    command "restored-verify" ["sh", "scripts/verify.sh"],
    inventoryCommand "restored-source-inventory" "baseline"]

def inventoryScript : String := r#"#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: check-inventory.sh EXPECTED_PATHS EXPECTED_SHA256" >&2
  exit 2
fi

EXPECTED_PATHS=$1
EXPECTED_SHA256=$2
TMP_ROOT=${TMPDIR:-/tmp}
ACTUAL_PATHS=$(mktemp "$TMP_ROOT/a12-qualification-paths.XXXXXX")
trap 'rm -f "$ACTUAL_PATHS"' EXIT HUP INT TERM

if find . -type l ! -path './target/*' -print | grep -q .; then
  echo "candidate tree contains a symbolic link" >&2
  exit 1
fi

find . -type f ! -path './target/*' -print | sed 's#^\./##' | LC_ALL=C sort > "$ACTUAL_PATHS"
diff -u "$EXPECTED_PATHS" "$ACTUAL_PATHS"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c "$EXPECTED_SHA256" >/dev/null
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c "$EXPECTED_SHA256" >/dev/null
else
  echo "qualification requires sha256sum or shasum" >&2
  exit 1
fi

cat "$EXPECTED_SHA256"
"#

def verifyPayloadsScript : String := r#"#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PACKET_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
cd "$PACKET_ROOT"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c PAYLOADS.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c PAYLOADS.sha256
else
  echo "qualification requires sha256sum or shasum" >&2
  exit 1
fi
"#

def resultTemplateText (sourceRevision candidateBaseRevision : String)
    (mutationPlanSha256 : Digest) (baseline : List FileDigest) (toolchain : List ToolchainSpec)
    (mutations : List MutationArtifact) : String :=
  let placeholder := String.ofList (List.replicate 64 '0')
  let fileJson (file : FileDigest) := Json.mkObj [
    ("path", file.path.asJson), ("sha256", file.sha256.asJson)]
  let commandJson (phase : String) (spec : CommandSpec) := Json.mkObj [
    ("id", toJson spec.id),
    ("argv", toJson spec.argv),
    ("exitStatus", toJson spec.expectedExitStatus),
    ("stdoutLog", toJson s!"logs/{phase}/{spec.id}.stdout"),
    ("stderrLog", toJson s!"logs/{phase}/{spec.id}.stderr")]
  let logsJson (phase : String) (commands : List CommandSpec) :=
    Json.arr (commands.flatMap (fun spec => [
      Json.mkObj [("path", toJson s!"logs/{phase}/{spec.id}.stdout"),
        ("sha256", toJson placeholder)],
      Json.mkObj [("path", toJson s!"logs/{phase}/{spec.id}.stderr"),
        ("sha256", toJson placeholder)]]) |>.toArray)
  let gateJson (phase : String) (commands : List CommandSpec) := Json.mkObj [
    ("outcome", toJson "passed"),
    ("commands", Json.arr (commands.map (commandJson phase)).toArray),
    ("rawLogs", logsJson phase commands),
    ("sourceFiles", Json.arr (baseline.map fileJson).toArray)]
  let mutationJson (entry : MutationArtifact × MutationDescriptor) :=
    let artifact := entry.1
    let descriptor := entry.2
    let phase := s!"mutation-{artifact.exercise}"
    Json.mkObj [
      ("exercise", toJson artifact.exercise),
      ("mutationId", toJson artifact.mutationId),
      ("predictionAttestedBeforePatch", toJson true),
      ("patch", artifact.patch.path.asJson),
      ("patchSha256", artifact.patch.sha256.asJson),
      ("commands", Json.arr (artifact.commands.map (commandJson phase)).toArray),
      ("rawLogs", logsJson phase artifact.commands),
      ("exitStatuses", toJson (artifact.commands.map (·.expectedExitStatus))),
      ("observedCaseResults", Json.arr
        (MutationResult.expectedMutationCaseResults descriptor |>.map
          MutationResult.CaseResult.asJson).toArray),
      ("observedAlgebraResults", Json.arr
        (MutationResult.expectedMutationAlgebraResults descriptor |>.map
          MutationResult.AlgebraResult.asJson).toArray),
      ("unexpectedDifferences", Json.arr #[]),
      ("outcome", toJson "matchedPrediction"),
      ("restoration", Json.mkObj [
        ("outcome", toJson "passed"), ("reversePatchApplied", toJson true)]),
      ("restoredSourceFiles", Json.arr (baseline.map fileJson).toArray)]
  (Json.mkObj [
    ("resultSchemaVersion", toJson MutationResult.resultSchemaVersion),
    ("packetId", toJson packetId),
    ("packetIndexSha256", toJson placeholder),
    ("sourceRevision", toJson sourceRevision),
    ("candidateBaseRevision", toJson candidateBaseRevision),
    ("assuranceClass", toJson "isolatedSessionAttestation"),
    ("isolationBoundary", toJson disposableIsolationBoundary),
    ("unresolvedQuestions", Json.arr #[]),
    ("mutationPlanId", toJson mutationPlan.id),
    ("mutationPlanSha256", mutationPlanSha256.asJson),
    ("capabilityId", toJson capability.id),
    ("baselineImplementationRevision", toJson baselineImplementationRevision),
    ("baselineSourceFiles", Json.arr (baseline.map fileJson).toArray),
    ("toolchain", Json.arr (toolchain.map ToolchainSpec.asJson).toArray),
    ("naturalGate", gateJson "natural" expectedNaturalCommands),
    ("mutations", Json.arr (mutations.zip mutationPlan.mutations |>.map mutationJson).toArray),
    ("finalRestorationGate", gateJson "final" expectedFinalCommands)]).pretty 100 ++ "\n"

def packetPrompt : String := r#"Work only from this packet and the frozen candidate tree it contains. Do not inspect a12-kernel-lean source, spec/, the A12 kernel, a12-dmkits, sibling semantic sources, web material about A12 semantics, or prior semantic conversation. This is qualification of an already implemented finite capability, not new semantics research.

Before execution, compare the SHA-256 of `PACKET.json` with the digest supplied out of band by the source maintainer, then run `./tools/verify-payloads.sh`. Do not call back into the Lean source checkout. In a fresh temporary workspace, copy this packet to `packet/`, copy `packet/baseline/` to `candidate/` while preserving executable bits, and create `result/`. Run every command from `candidate/` in the exact order and argv recorded in PACKET.json, using its `executionProfile`. The natural gate temporarily applies the observer-only patch, captures the baseline eight cases and complete verdict algebra, removes the observer, verifies the implementation, and ends on the restored path-and-byte inventory. Attest the prediction before applying each semantic patch, one mutation at a time. Capture each command's stdout and stderr verbatim under `result/logs/`, record exit statuses, copy each mutation observer's parsed case/algebra results into RESULT.json, reverse the patch, verify the implementation and then the complete restored path-and-byte inventory, and never commit a mutated implementation.

Use RESULT.template.json only as a shape and expected-observation aid: replace the packet-index and log-digest placeholders with exact digests of the bytes actually used or returned. The record's `isolatedSessionAttestation` class is intentional; the source-side packet preflight is retained separately. Stop on any missing, additional, reordered, or unexpected result. Do not explain away a mismatch or research the kernel; preserve the artifacts and classify it for the source maintainer. After all seven exercises and the final restoration gate pass, copy the complete result directory into the Rust repository under the location requested by the source maintainer, verify the Rust worktree contains no mutation, commit only the qualification record, and report that commit.
"#

def runbook : String := r#"# Flat Rust mutation qualification packet

This transient packet qualifies only `flat-validation-empty-logic-v1` at the pinned natural Rust revision. It is source-maintainer test material, not A12 semantics, kernel evidence, a transferred Lean proof, release approval, or an extension of the original cold bundle.

Read `PROMPT.md`, then inspect `PACKET.json`. The index binds the frozen Rust build/test input closure (Cargo and toolchain files, source, tests, verification scripts, and the complete consumed handover), exact observer, an observer-only baseline patch and expected observation, seven combined observer/semantic patches, expected mutation observations, complete natural, instrumented, and mutant source inventories, command policy, and every payload file by SHA-256. Unrelated reports, prompts, and agent instructions are deliberately outside the executable closure. The observer reads the frozen canonical conformance suite and request fixtures from the handed-over source tree and rejects a missing, additional, or reordered case. The baseline observation and exercises 5 and 6 return all 32 ordered verdict-algebra cells; every observation returns all eight capability cases.

Use a temporary `packet/`, `candidate/`, `result/` workspace. Do not run a patch in the tracked Rust checkout. `tools/check-inventory.sh` rejects source-tree symlinks, missing/additional files outside `target/`, and path-or-byte drift; packet construction separately preserves and checks frozen Git executable modes. The returned RESULT.json and raw logs are checked later by `checkMutationQualification`; narrative success is not accepted as the record.
"#

structure ExpectedAuxiliaryContent where
  path : PortablePath
  content : String
  deriving Repr, DecidableEq

private def expectedAuxiliary (path content : String) : Except String ExpectedAuxiliaryContent := do
  pure {
    path := ← portablePath path s!"expected auxiliary path '{path}'"
    content }

/-- Reconstruct every source-owned auxiliary payload from the typed packet index. This keeps scripts, inventories, prompt, template, and payload manifest inside the same drift check as patches and observations. -/
def expectedAuxiliaryContents (index : Index) : Except String (List ExpectedAuxiliaryContent) := do
  let mut contents : List ExpectedAuxiliaryContent := [
    ← expectedAuxiliary "expected/baseline.paths" (inventoryPaths index.baselineResultFiles),
    ← expectedAuxiliary "expected/baseline.sha256" (inventoryDigests index.baselineResultFiles),
    ← expectedAuxiliary "expected/instrumented-baseline.paths"
      (inventoryPaths index.instrumentedBaselineSourceFiles),
    ← expectedAuxiliary "expected/instrumented-baseline.sha256"
      (inventoryDigests index.instrumentedBaselineSourceFiles)]
  for (artifact, descriptor) in index.mutations.zip mutationPlan.mutations do
    let stem := mutationFileStem descriptor
    contents := contents ++ [
      ← expectedAuxiliary s!"expected/{stem}.paths"
        (inventoryPaths artifact.mutatedSourceFiles),
      ← expectedAuxiliary s!"expected/{stem}.sha256"
        (inventoryDigests artifact.mutatedSourceFiles)]
  contents := contents ++ [
    ← expectedAuxiliary "tools/check-inventory.sh" inventoryScript,
    ← expectedAuxiliary "tools/verify-payloads.sh" verifyPayloadsScript,
    ← expectedAuxiliary "PROMPT.md" packetPrompt,
    ← expectedAuxiliary "README.md" runbook,
    ← expectedAuxiliary "RESULT.template.json"
      (resultTemplateText index.sourceRevision index.candidateBaseRevision
        index.mutationPlan.sha256 index.baselineResultFiles index.toolchain index.mutations)]
  let payloadsBeforeManifest := index.payloadFiles.take (index.payloadFiles.length - 1)
  contents := contents ++ [
    ← expectedAuxiliary "PAYLOADS.sha256" (inventoryDigests payloadsBeforeManifest)]
  pure contents

private def ensureNewDirectory (path : System.FilePath) : IO Unit := do
  if ← System.FilePath.pathExists path then
    throw (IO.userError s!"qualification packet output already exists: '{path}'")
  IO.FS.createDirAll path

private def checkCandidateClean (candidateRoot : System.FilePath) : IO Unit := do
  let status ← processOutput "git"
    #["-C", candidateRoot.toString, "status", "--short", "--untracked-files=all"]
  if !status.isEmpty then
    throw (IO.userError "candidate repository must be visibly clean before packet export")
  let objectType ← processOutput "git"
    #["-C", candidateRoot.toString, "cat-file", "-t", baselineImplementationRevision]
  if objectType.trimAscii.toString != "commit" then
    throw (IO.userError "frozen candidate revision is not a Git commit")

private def gitHead (root : System.FilePath) (label : String) : IO String := do
  let revision ← processOutput "git" #["-C", root.toString, "rev-parse", "HEAD"]
  let revision := revision.trimAscii.toString
  if revision.length != 40 then
    throw (IO.userError s!"{label} HEAD is not a full Git revision")
  pure revision

def candidateHead (candidateRoot : System.FilePath) : IO String :=
  gitHead candidateRoot "candidate"

private def requireCleanCheckout (root : System.FilePath) (label : String) : IO Unit := do
  let status ← processOutput "git"
    #["-C", root.toString, "status", "--short", "--untracked-files=all"]
  if !status.isEmpty then
    throw (IO.userError s!"{label} checkout must be clean for an exportable qualification packet")

def verifySourceCheckout (projectRoot : System.FilePath) (index : Index)
    (allowDirty : Bool := false) : IO Unit := do
  let head ← gitHead projectRoot sourceProjectName
  if head != index.sourceRevision then
    throw (IO.userError
      s!"qualification packet requires {sourceProjectName} revision {index.sourceRevision}, found {head}")
  if !allowDirty then requireCleanCheckout projectRoot sourceProjectName

def verifyFrozenBaseline (candidateRoot packetRoot : System.FilePath) (index : Index) : IO Unit := do
  checkCandidateClean candidateRoot
  let entries ← gitEntriesAt candidateRoot baselineImplementationRevision
  let expectedIdentity := index.baselineSourceFiles.map fun file =>
    (if file.executable then "100755" else "100644", file.candidatePath)
  let actualIdentity := entries.map fun entry => (entry.mode, entry.path)
  if actualIdentity != expectedIdentity then
    throw (IO.userError
      "qualification packet baseline inventory differs from the frozen Git revision")
  for (entry, source) in entries.zip index.baselineSourceFiles do
    let frozen ← processOutput "git"
      #["-C", candidateRoot.toString, "show",
        s!"{baselineImplementationRevision}:{entry.path.toString}"]
    let packetCopy ← IO.FS.readFile (packetRoot / source.packetPath.toString)
    if packetCopy != frozen then
      throw (IO.userError
        s!"qualification packet baseline bytes differ from frozen Git path '{entry.path}'")

  let candidateBaseType ← processOutput "git"
    #["-C", candidateRoot.toString, "cat-file", "-t", index.candidateBaseRevision]
  if candidateBaseType.trimAscii.toString != "commit" then
    throw (IO.userError "packet-pinned candidate base revision is not a Git commit")
  let currentHead ← gitHead candidateRoot "candidate"
  let _ ← processOutput "git"
    #["-C", candidateRoot.toString, "merge-base", "--is-ancestor",
      index.candidateBaseRevision, currentHead]
  for revision in [index.candidateBaseRevision, currentHead] do
    let currentEntries ← gitEntriesAt candidateRoot revision
    let currentIdentity := currentEntries.map fun entry => (entry.mode, entry.path)
    if currentIdentity != expectedIdentity then
      throw (IO.userError
        s!"candidate build-input closure at revision {revision} differs from the frozen baseline")
    for (entry, source) in currentEntries.zip index.baselineSourceFiles do
      let currentBytes ← processOutput "git"
        #["-C", candidateRoot.toString, "show", s!"{revision}:{entry.path.toString}"]
      let packetCopy ← IO.FS.readFile (packetRoot / source.packetPath.toString)
      if currentBytes != packetCopy then
        throw (IO.userError
          s!"candidate build input '{entry.path}' at revision {revision} differs from the frozen baseline")

private def writeAuxiliary (packetRoot : System.FilePath) (pathText content : String)
    (executable := false) : IO FileDigest := do
  let path ← portablePath pathText s!"auxiliary packet path '{pathText}'" |> IO.ofExcept
  writeFile packetRoot path content executable

def exportPacket (projectRoot candidateRoot packetRoot : System.FilePath)
    (allowDirtySource : Bool := false) : IO Index := do
  ensureNewDirectory packetRoot
  try
    checkCandidateClean candidateRoot
    if !allowDirtySource then requireCleanCheckout projectRoot sourceProjectName
    let sourceRevision ← gitHead projectRoot sourceProjectName
    let candidateBaseRevision ← gitHead candidateRoot "candidate"
    let entries ← gitEntriesAt candidateRoot baselineImplementationRevision
    let baselineSourceFiles ← entries.mapM (exportBaselineFile candidateRoot packetRoot)
    let baselineResultFiles := baselineSourceFiles.map fun file => {
      path := file.candidatePath, sha256 := file.sha256 }
    let libPath ← portablePath "src/lib.rs" "Rust library path" |> IO.ofExcept
    let baselineLib ← processOutput "git"
      #["-C", candidateRoot.toString, "show",
        s!"{baselineImplementationRevision}:{libPath.toString}"]
    let observerSourcePath := projectRoot /
      "A12Kernel/Qualification/Assets/flat_validation_observer.rs"
    let observerContent ← IO.FS.readFile observerSourcePath
    let observerPacketPath ← portablePath "assets/flat_validation_observer.rs"
      "observer packet path" |> IO.ofExcept
    let observer ← writeFile packetRoot observerPacketPath observerContent
    let observerCandidatePath ← portablePath observerCandidatePathText
      "observer candidate path" |> IO.ofExcept
    let baselineObserverPatchContent ← sourceOwnedObserverPatch observerContent |> IO.ofExcept
    let baselineObserverPatch ← writeAuxiliary packetRoot "patches/00-observer.patch"
      baselineObserverPatchContent
    let expectedBaselineObservation ← writeAuxiliary packetRoot
      "expected/00-baseline.observation.json"
      (expectedBaselineObservationJson.pretty 100 ++ "\n")
    let planPacketPath ← portablePath "reference/flat-validation-empty-logic-v1.mutation-plan.json"
      "mutation plan packet path" |> IO.ofExcept
    let planContent ← IO.FS.readFile
      (projectRoot / "reference/flat-validation-empty-logic-v1.mutation-plan.json")
    let mutationPlanFile ← writeFile packetRoot planPacketPath planContent
    let toolchain ← ["rustc", "cargo"].mapM (toolVersion candidateRoot)
    let projections ← sourceOwnedMutationProjections baselineLib observerContent |> IO.ofExcept
    let mut mutationArtifacts : List MutationArtifact := []
    let mut auxiliaryFiles : List FileDigest := []
    let instrumentedBaselineSourceFiles := sortedFiles (baselineResultFiles ++ [{
      path := observerCandidatePath, sha256 := observer.sha256 }])
    let baselinePaths ← writeAuxiliary packetRoot "expected/baseline.paths"
      (inventoryPaths baselineResultFiles)
    let baselineDigests ← writeAuxiliary packetRoot "expected/baseline.sha256"
      (inventoryDigests baselineResultFiles)
    let instrumentedPaths ← writeAuxiliary packetRoot "expected/instrumented-baseline.paths"
      (inventoryPaths instrumentedBaselineSourceFiles)
    let instrumentedDigests ← writeAuxiliary packetRoot "expected/instrumented-baseline.sha256"
      (inventoryDigests instrumentedBaselineSourceFiles)
    auxiliaryFiles := auxiliaryFiles ++ [baselinePaths, baselineDigests,
      instrumentedPaths, instrumentedDigests]
    for projection in projections do
      let stem := mutationFileStem projection.descriptor
      let patch ← writeAuxiliary packetRoot s!"patches/{stem}.patch" projection.patch
      let expectedObservation ← writeAuxiliary packetRoot
        s!"expected/{stem}.observation.json"
        ((observationJson projection.descriptor).pretty 100 ++ "\n")
      let mutatedLibDigest ← IO.FS.withTempFile fun handle path => do
        handle.putStr projection.mutatedLibrary
        handle.flush
        hashFile path
      let mutatedBase ← replaceSourceDigest baselineResultFiles libPath mutatedLibDigest |> IO.ofExcept
      let mutatedFiles := sortedFiles (mutatedBase ++ [{
        path := observerCandidatePath, sha256 := observer.sha256 }])
      let mutatedPaths ← writeAuxiliary packetRoot s!"expected/{stem}.paths"
        (inventoryPaths mutatedFiles)
      let mutatedDigests ← writeAuxiliary packetRoot s!"expected/{stem}.sha256"
        (inventoryDigests mutatedFiles)
      auxiliaryFiles := auxiliaryFiles ++ [mutatedPaths, mutatedDigests]
      mutationArtifacts := mutationArtifacts ++ [{
        exercise := projection.descriptor.mechanism.exercise
        mutationId := projection.descriptor.mechanism.tag
        patch
        expectedObservation
        mutatedSourceFiles := mutatedFiles
        commands := expectedMutationCommands projection.descriptor }]
    let inventoryTool ← writeAuxiliary packetRoot "tools/check-inventory.sh" inventoryScript true
    let payloadVerifier ← writeAuxiliary packetRoot "tools/verify-payloads.sh"
      verifyPayloadsScript true
    let prompt ← writeAuxiliary packetRoot "PROMPT.md" packetPrompt
    let readme ← writeAuxiliary packetRoot "README.md" runbook
    auxiliaryFiles := auxiliaryFiles ++ [inventoryTool, payloadVerifier, prompt, readme]
    let templateContent := resultTemplateText sourceRevision candidateBaseRevision
      mutationPlanFile.sha256 baselineResultFiles toolchain mutationArtifacts
    let template ← writeAuxiliary packetRoot "RESULT.template.json" templateContent
    auxiliaryFiles := auxiliaryFiles ++ [template]
    let sourcePayloads := baselineSourceFiles.map fun file => {
      path := file.packetPath, sha256 := file.sha256 }
    let payloadFilesBeforeManifest := [mutationPlanFile, observer, baselineObserverPatch,
        expectedBaselineObservation] ++ sourcePayloads ++
      mutationArtifacts.flatMap (fun mutation => [mutation.patch, mutation.expectedObservation]) ++
      auxiliaryFiles
    let payloadManifest ← writeAuxiliary packetRoot "PAYLOADS.sha256"
      (inventoryDigests payloadFilesBeforeManifest)
    auxiliaryFiles := auxiliaryFiles ++ [payloadManifest]
    let payloadFiles := payloadFilesBeforeManifest ++ [payloadManifest]
    let index : Index := {
      schemaVersion := packetSchemaVersion
      id := packetId
      sourceRevision
      candidateBaseRevision
      compatibility := expectedCompatibility
      executionProfile := expectedExecutionProfile
      mutationPlan := mutationPlanFile
      baselineRevision := baselineImplementationRevision
      baselineSourceFiles
      observer
      baselineObserverPatch
      expectedBaselineObservation
      instrumentedBaselineSourceFiles
      toolchain
      naturalGateCommands := expectedNaturalCommands
      mutations := mutationArtifacts
      finalRestorationGateCommands := expectedFinalCommands
      auxiliaryFiles
      payloadFiles }
    IO.ofExcept index.validate
    IO.FS.writeFile (packetRoot / "PACKET.json") (index.asJson.pretty 100 ++ "\n")
    pure index
  catch error =>
    if ← System.FilePath.pathExists packetRoot then IO.FS.removeDirAll packetRoot
    throw error

end A12Kernel.Qualification.RustPacket
