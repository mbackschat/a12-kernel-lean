import A12Kernel.Evidence.FlatProtocolBridge
import A12Kernel.Qualification.Artifact
import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! # Strict post-cold mutation qualification results

This module defines the closed language-neutral result record returned by an independent
candidate session and validates its pure qualification metadata against the typed mutation
plan. Filesystem resolution and digest recomputation belong to the separate qualification
checker. This record is not kernel evidence, a proof about the candidate, or part of the
trusted semantics library.
-/

namespace A12Kernel.Qualification.MutationResult

open Lean
open A12Kernel
open A12Kernel.Evidence.FlatProtocolBridge
open A12Kernel.Qualification.Artifact

def resultSchemaVersion : Nat := mutationQualificationResultSchemaVersion

structure ToolchainRecord where
  name : String
  version : String
  deriving Repr, DecidableEq

structure CommandRecord where
  id : String
  argv : List String
  exitStatus : Nat
  stdoutLog : PortablePath
  stderrLog : PortablePath
  deriving Repr, DecidableEq

structure CaseResult where
  caseId : String
  verdict : Verdict
  deriving Repr, DecidableEq

structure AlgebraResult where
  connective : VerdictConnective
  left : Verdict
  right : Verdict
  verdict : Verdict
  deriving Repr, DecidableEq

/-- Parsed stdout of one packet-owned observer invocation. Keeping this distinct from the typed expectation prevents a replay record from substituting predicted values for captured values. -/
structure Observation where
  exercise : Nat
  caseResults : List CaseResult
  algebraResults : List AlgebraResult
  deriving Repr, DecidableEq

inductive GateOutcome where
  | passed
  | failed
  deriving Repr, DecidableEq

inductive MutationOutcome where
  | matchedPrediction
  | unexpectedDifference
  | notRun
  deriving Repr, DecidableEq

inductive AssuranceClass where
  | isolatedSessionAttestation
  | sourceExecutedReplay
  deriving Repr, DecidableEq

structure GateRecord where
  outcome : GateOutcome
  commands : List CommandRecord
  rawLogs : List FileDigest
  sourceFiles : List FileDigest
  deriving Repr, DecidableEq

structure RestorationRecord where
  outcome : GateOutcome
  reversePatchApplied : Bool
  deriving Repr, DecidableEq

structure MutationRecord where
  exercise : Nat
  mutationId : String
  predictionAttestedBeforePatch : Bool
  patch : PortablePath
  patchSha256 : Digest
  commands : List CommandRecord
  rawLogs : List FileDigest
  exitStatuses : List Nat
  observedCaseResults : List CaseResult
  observedAlgebraResults : List AlgebraResult
  unexpectedDifferences : List String
  outcome : MutationOutcome
  restoration : RestorationRecord
  restoredSourceFiles : List FileDigest
  deriving Repr, DecidableEq

structure Result where
  schemaVersion : Nat
  packetId : String
  packetIndexSha256 : Digest
  sourceRevision : String
  candidateBaseRevision : String
  assuranceClass : AssuranceClass
  isolationBoundary : String
  unresolvedQuestions : List String
  mutationPlanId : String
  mutationPlanSha256 : Digest
  capabilityId : String
  baselineImplementationRevision : String
  baselineSourceFiles : List FileDigest
  toolchain : List ToolchainRecord
  naturalGate : GateRecord
  mutations : List MutationRecord
  finalRestorationGate : GateRecord
  deriving Repr, DecidableEq

private def requiredJson (json : Json) (name context : String) : Except String Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error _ => throw s!"{context}: missing member '{name}'"

private def required [FromJson α] (json : Json) (name context : String) : Except String α := do
  let value ← requiredJson json name context
  match fromJson? value with
  | .ok decoded => pure decoded
  | .error _ => throw s!"{context}: member '{name}' has the wrong type"

private def requireObject (json : Json) (allowed : List String)
    (context : String) : Except String Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => throw s!"{context}: expected an object"
  for (name, _) in object.toList do
    if !allowed.contains name then
      throw s!"{context}: unknown member '{name}'"

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else firstDuplicate? rest

private def nonempty (value context : String) : Except String String := do
  if value.isEmpty then throw s!"{context}: must not be empty"
  pure value

private def parsePortablePath (value context : String) : Except String PortablePath :=
  match PortablePath.parse value with
  | .ok path => pure path
  | .error error => throw s!"{context}: {error}"

private def parseDigest (value context : String) : Except String Digest :=
  match Digest.parse value with
  | .ok digest => pure digest
  | .error error => throw s!"{context}: {error}"

private def parseVerdict (json : Json) (context : String) : Except String Verdict := do
  let tag : String ← required json "tag" context
  match tag with
  | "notFired" =>
      requireObject json ["tag"] context
      pure .notFired
  | "unknown" =>
      requireObject json ["tag"] context
      pure .unknown
  | "fired" =>
      requireObject json ["tag", "polarity"] context
      let polarity : String ← required json "polarity" context
      match polarity with
      | "value" => pure (.fired .value)
      | "omission" => pure (.fired .omission)
      | other => throw s!"{context}: unsupported polarity '{other}'"
  | other => throw s!"{context}: unsupported verdict '{other}'"

private def parseConnective (tag context : String) : Except String VerdictConnective :=
  match tag with
  | "and" => pure .and
  | "or" => pure .or
  | other => throw s!"{context}: unsupported connective '{other}'"

private def parseFileDigest (json : Json) (context : String) : Except String FileDigest :=
  FileDigest.parseJson json context

private def parseFileDigests (json : Json) (name context : String) :
    Except String (List FileDigest) := do
  let values : List Json ← required json name context
  let parsed ← values.zipIdx.mapM fun (value, index) =>
    parseFileDigest value s!"{context} {name}[{index}]"
  match FileDigest.validateInventory parsed with
  | .ok _ => pure parsed
  | .error error => throw s!"{context}: invalid {name}: {error}"

private def parseToolchain (json : Json) (index : Nat) : Except String ToolchainRecord := do
  let context := s!"result toolchain[{index}]"
  requireObject json ["name", "version"] context
  pure {
    name := ← nonempty (← required json "name" context) s!"{context} name"
    version := ← nonempty (← required json "version" context) s!"{context} version" }

private def parseCommand (json : Json) (context : String) : Except String CommandRecord := do
  requireObject json ["id", "argv", "exitStatus", "stdoutLog", "stderrLog"] context
  let id ← nonempty (← required json "id" context) s!"{context} id"
  let argv : List String ← required json "argv" context
  if argv.isEmpty || argv.any (·.isEmpty) then
    throw s!"{context}: argv must contain only nonempty arguments"
  let stdoutLog ← parsePortablePath (← required json "stdoutLog" context)
    s!"{context}: invalid stdout log"
  let stderrLog ← parsePortablePath (← required json "stderrLog" context)
    s!"{context}: invalid stderr log"
  pure {
    id
    argv
    exitStatus := ← required json "exitStatus" context
    stdoutLog
    stderrLog }

private def parseCommands (json : Json) (name context : String) :
    Except String (List CommandRecord) := do
  let values : List Json ← required json name context
  let parsed ← values.zipIdx.mapM fun (value, index) =>
    parseCommand value s!"{context} {name}[{index}]"
  if parsed.isEmpty then throw s!"{context}: {name} must not be empty"
  match firstDuplicate? (parsed.map (·.id)) with
  | some duplicate => throw s!"{context}: duplicate command id '{duplicate}'"
  | none => pure parsed

private def parseCaseResult (json : Json) (context : String) : Except String CaseResult := do
  requireObject json ["caseId", "verdict"] context
  pure {
    caseId := ← nonempty (← required json "caseId" context) s!"{context} caseId"
    verdict := ← parseVerdict (← requiredJson json "verdict" context) s!"{context} verdict" }

private def parseCaseResults (json : Json) (name context : String) :
    Except String (List CaseResult) := do
  let values : List Json ← required json name context
  let parsed ← values.zipIdx.mapM fun (value, index) =>
    parseCaseResult value s!"{context} {name}[{index}]"
  match firstDuplicate? (parsed.map (·.caseId)) with
  | some duplicate => throw s!"{context}: duplicate case result '{duplicate}'"
  | none => pure parsed

private def parseAlgebraResult (json : Json) (context : String) : Except String AlgebraResult := do
  requireObject json ["connective", "left", "right", "verdict"] context
  pure {
    connective := ← parseConnective (← required json "connective" context) context
    left := ← parseVerdict (← requiredJson json "left" context) s!"{context} left"
    right := ← parseVerdict (← requiredJson json "right" context) s!"{context} right"
    verdict := ← parseVerdict (← requiredJson json "verdict" context) s!"{context} verdict" }

private def parseAlgebraResults (json : Json) (name context : String) :
    Except String (List AlgebraResult) := do
  let values : List Json ← required json name context
  values.zipIdx.mapM fun (value, index) =>
    parseAlgebraResult value s!"{context} {name}[{index}]"

/-- Parse the closed observation object shared by the natural and mutant observer commands. -/
def parseObservationJson (json : Json) : Except String Observation := do
  let context := "mutation qualification observation"
  requireObject json ["observationSchemaVersion", "exercise", "caseResults",
    "algebraResults"] context
  let schemaVersion : Nat ← required json "observationSchemaVersion" context
  if schemaVersion != 1 then
    throw s!"{context}: unsupported schema version {schemaVersion}"
  pure {
    exercise := ← required json "exercise" context
    caseResults := ← parseCaseResults json "caseResults" context
    algebraResults := ← parseAlgebraResults json "algebraResults" context }

/-- Parse an observation through the duplicate-member-rejecting JSON boundary. -/
def parseObservationText (input : String) : Except String Observation := do
  let json ← match A12Kernel.Reference.StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"invalid strict qualification-observation JSON: {repr error}"
  parseObservationJson json

private def parseGateOutcome (tag context : String) : Except String GateOutcome :=
  match tag with
  | "passed" => pure .passed
  | "failed" => pure .failed
  | other => throw s!"{context}: unsupported gate outcome '{other}'"

private def parseMutationOutcome (tag context : String) : Except String MutationOutcome :=
  match tag with
  | "matchedPrediction" => pure .matchedPrediction
  | "unexpectedDifference" => pure .unexpectedDifference
  | "notRun" => pure .notRun
  | other => throw s!"{context}: unsupported mutation outcome '{other}'"

private def parseAssuranceClass (tag context : String) : Except String AssuranceClass :=
  match tag with
  | "isolatedSessionAttestation" => pure .isolatedSessionAttestation
  | "sourceExecutedReplay" => pure .sourceExecutedReplay
  | other => throw s!"{context}: unsupported assurance class '{other}'"

private def parseGate (json : Json) (context : String) : Except String GateRecord := do
  requireObject json ["outcome", "commands", "rawLogs", "sourceFiles"] context
  pure {
    outcome := ← parseGateOutcome (← required json "outcome" context) context
    commands := ← parseCommands json "commands" context
    rawLogs := ← parseFileDigests json "rawLogs" context
    sourceFiles := ← parseFileDigests json "sourceFiles" context }

private def parseRestoration (json : Json) (context : String) : Except String RestorationRecord := do
  requireObject json ["outcome", "reversePatchApplied"] context
  pure {
    outcome := ← parseGateOutcome (← required json "outcome" context) context
    reversePatchApplied := ← required json "reversePatchApplied" context }

private def parseMutation (json : Json) (index : Nat) : Except String MutationRecord := do
  let context := s!"result mutations[{index}]"
  requireObject json ["exercise", "mutationId", "predictionAttestedBeforePatch", "patch",
    "patchSha256", "commands", "rawLogs", "exitStatuses", "observedCaseResults",
    "observedAlgebraResults", "unexpectedDifferences", "outcome", "restoration",
    "restoredSourceFiles"] context
  let patch ← parsePortablePath (← required json "patch" context)
    s!"{context}: invalid patch path"
  let patchSha256 ← parseDigest (← required json "patchSha256" context)
    s!"{context}: invalid patchSha256"
  pure {
    exercise := ← required json "exercise" context
    mutationId := ← nonempty (← required json "mutationId" context) s!"{context} mutationId"
    predictionAttestedBeforePatch := ← required json "predictionAttestedBeforePatch" context
    patch
    patchSha256
    commands := ← parseCommands json "commands" context
    rawLogs := ← parseFileDigests json "rawLogs" context
    exitStatuses := ← required json "exitStatuses" context
    observedCaseResults := ← parseCaseResults json "observedCaseResults" context
    observedAlgebraResults := ← parseAlgebraResults json "observedAlgebraResults" context
    unexpectedDifferences := ← required json "unexpectedDifferences" context
    outcome := ← parseMutationOutcome (← required json "outcome" context) context
    restoration := ← parseRestoration (← requiredJson json "restoration" context)
      s!"{context} restoration"
    restoredSourceFiles := ← parseFileDigests json "restoredSourceFiles" context }

def parseResultJson (json : Json) : Except String Result := do
  let context := "mutation qualification result"
  requireObject json ["resultSchemaVersion", "packetId", "packetIndexSha256",
    "sourceRevision", "candidateBaseRevision", "assuranceClass", "isolationBoundary",
    "unresolvedQuestions", "mutationPlanId", "mutationPlanSha256", "capabilityId",
    "baselineImplementationRevision", "baselineSourceFiles", "toolchain", "naturalGate",
    "mutations", "finalRestorationGate"] context
  let packetIndexSha256 ← parseDigest (← required json "packetIndexSha256" context)
    s!"{context}: invalid packetIndexSha256"
  let mutationPlanSha256 ← parseDigest (← required json "mutationPlanSha256" context)
    s!"{context}: invalid mutationPlanSha256"
  let toolchainJson : List Json ← required json "toolchain" context
  let mutationJson : List Json ← required json "mutations" context
  pure {
    schemaVersion := ← required json "resultSchemaVersion" context
    packetId := ← nonempty (← required json "packetId" context) s!"{context} packetId"
    packetIndexSha256
    sourceRevision := ← nonempty (← required json "sourceRevision" context)
      s!"{context} sourceRevision"
    candidateBaseRevision := ← nonempty (← required json "candidateBaseRevision" context)
      s!"{context} candidateBaseRevision"
    assuranceClass := ← parseAssuranceClass (← required json "assuranceClass" context) context
    isolationBoundary := ← nonempty (← required json "isolationBoundary" context)
      s!"{context} isolationBoundary"
    unresolvedQuestions := ← required json "unresolvedQuestions" context
    mutationPlanId := ← nonempty (← required json "mutationPlanId" context)
      s!"{context} mutationPlanId"
    mutationPlanSha256
    capabilityId := ← nonempty (← required json "capabilityId" context)
      s!"{context} capabilityId"
    baselineImplementationRevision := ← nonempty
      (← required json "baselineImplementationRevision" context)
      s!"{context} baselineImplementationRevision"
    baselineSourceFiles := ← parseFileDigests json "baselineSourceFiles" context
    toolchain := ← toolchainJson.zipIdx.mapM fun (value, index) => parseToolchain value index
    naturalGate := ← parseGate (← requiredJson json "naturalGate" context) "natural gate"
    mutations := ← mutationJson.zipIdx.mapM fun (value, index) => parseMutation value index
    finalRestorationGate := ← parseGate
      (← requiredJson json "finalRestorationGate" context) "final restoration gate" }

def parseResultText (input : String) : Except String Result := do
  let json ← match A12Kernel.Reference.StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"invalid strict qualification-result JSON: {repr error}"
  parseResultJson json

def verdictJson : Verdict → Json
  | .notFired => Json.mkObj [("tag", toJson "notFired")]
  | .unknown => Json.mkObj [("tag", toJson "unknown")]
  | .fired .value =>
      Json.mkObj [("tag", toJson "fired"), ("polarity", toJson "value")]
  | .fired .omission =>
      Json.mkObj [("tag", toJson "fired"), ("polarity", toJson "omission")]

def ToolchainRecord.asJson (toolchain : ToolchainRecord) : Json :=
  Json.mkObj [("name", toJson toolchain.name), ("version", toJson toolchain.version)]

def CommandRecord.asJson (command : CommandRecord) : Json :=
  Json.mkObj [
    ("id", toJson command.id),
    ("argv", toJson command.argv),
    ("exitStatus", toJson command.exitStatus),
    ("stdoutLog", toJson command.stdoutLog.toString),
    ("stderrLog", toJson command.stderrLog.toString)]

def CaseResult.asJson (result : CaseResult) : Json :=
  Json.mkObj [("caseId", toJson result.caseId), ("verdict", verdictJson result.verdict)]

def AlgebraResult.asJson (result : AlgebraResult) : Json :=
  Json.mkObj [
    ("connective", toJson result.connective.tag),
    ("left", verdictJson result.left),
    ("right", verdictJson result.right),
    ("verdict", verdictJson result.verdict)]

def Observation.asJson (observation : Observation) : Json :=
  Json.mkObj [
    ("observationSchemaVersion", toJson 1),
    ("exercise", toJson observation.exercise),
    ("caseResults", Json.arr (observation.caseResults.map CaseResult.asJson).toArray),
    ("algebraResults", Json.arr
      (observation.algebraResults.map AlgebraResult.asJson).toArray)]

def GateOutcome.tag : GateOutcome → String
  | .passed => "passed"
  | .failed => "failed"

def MutationOutcome.tag : MutationOutcome → String
  | .matchedPrediction => "matchedPrediction"
  | .unexpectedDifference => "unexpectedDifference"
  | .notRun => "notRun"

def AssuranceClass.tag : AssuranceClass → String
  | .isolatedSessionAttestation => "isolatedSessionAttestation"
  | .sourceExecutedReplay => "sourceExecutedReplay"

def GateRecord.asJson (gate : GateRecord) : Json :=
  Json.mkObj [
    ("outcome", toJson gate.outcome.tag),
    ("commands", Json.arr (gate.commands.map CommandRecord.asJson).toArray),
    ("rawLogs", Json.arr (gate.rawLogs.map Artifact.FileDigest.asJson).toArray),
    ("sourceFiles", Json.arr (gate.sourceFiles.map Artifact.FileDigest.asJson).toArray)]

def RestorationRecord.asJson (restoration : RestorationRecord) : Json :=
  Json.mkObj [
    ("outcome", toJson restoration.outcome.tag),
    ("reversePatchApplied", toJson restoration.reversePatchApplied)]

def MutationRecord.asJson (mutation : MutationRecord) : Json :=
  Json.mkObj [
    ("exercise", toJson mutation.exercise),
    ("mutationId", toJson mutation.mutationId),
    ("predictionAttestedBeforePatch", toJson mutation.predictionAttestedBeforePatch),
    ("patch", toJson mutation.patch.toString),
    ("patchSha256", mutation.patchSha256.asJson),
    ("commands", Json.arr (mutation.commands.map CommandRecord.asJson).toArray),
    ("rawLogs", Json.arr (mutation.rawLogs.map Artifact.FileDigest.asJson).toArray),
    ("exitStatuses", toJson mutation.exitStatuses),
    ("observedCaseResults", Json.arr (mutation.observedCaseResults.map CaseResult.asJson).toArray),
    ("observedAlgebraResults",
      Json.arr (mutation.observedAlgebraResults.map AlgebraResult.asJson).toArray),
    ("unexpectedDifferences", toJson mutation.unexpectedDifferences),
    ("outcome", toJson mutation.outcome.tag),
    ("restoration", mutation.restoration.asJson),
    ("restoredSourceFiles",
      Json.arr (mutation.restoredSourceFiles.map Artifact.FileDigest.asJson).toArray)]

def Result.asJson (result : Result) : Json :=
  Json.mkObj [
    ("resultSchemaVersion", toJson result.schemaVersion),
    ("packetId", toJson result.packetId),
    ("packetIndexSha256", result.packetIndexSha256.asJson),
    ("sourceRevision", toJson result.sourceRevision),
    ("candidateBaseRevision", toJson result.candidateBaseRevision),
    ("assuranceClass", toJson result.assuranceClass.tag),
    ("isolationBoundary", toJson result.isolationBoundary),
    ("unresolvedQuestions", toJson result.unresolvedQuestions),
    ("mutationPlanId", toJson result.mutationPlanId),
    ("mutationPlanSha256", result.mutationPlanSha256.asJson),
    ("capabilityId", toJson result.capabilityId),
    ("baselineImplementationRevision", toJson result.baselineImplementationRevision),
    ("baselineSourceFiles",
      Json.arr (result.baselineSourceFiles.map Artifact.FileDigest.asJson).toArray),
    ("toolchain", Json.arr (result.toolchain.map ToolchainRecord.asJson).toArray),
    ("naturalGate", result.naturalGate.asJson),
    ("mutations", Json.arr (result.mutations.map MutationRecord.asJson).toArray),
    ("finalRestorationGate", result.finalRestorationGate.asJson)]

structure ExpectedPacket where
  packetId : String
  packetIndexSha256 : Digest
  sourceRevision : String
  candidateBaseRevision : String
  assuranceClass : AssuranceClass
  isolationBoundary : String
  mutationPlanSha256 : Digest
  baselineImplementationRevision : String
  baselineSourceFiles : List FileDigest
  toolchain : List ToolchainRecord
  patches : List FileDigest
  deriving Repr, DecidableEq

private def expectedCaseResults (mutation : MutationDescriptor) : List CaseResult :=
  capability.cases.map fun case =>
    let verdict := match mutation.expectedCaseChanges.find? (·.caseId == case.id) with
      | some change => change.mutantVerdict
      | none => case.expectedVerdict
    { caseId := case.id, verdict }

private def expectedAlgebraResults (mutation : MutationDescriptor) : List AlgebraResult :=
  match mutation.mechanism.algebraMutation? with
  | none => []
  | some algebraMutation =>
      VerdictAlgebraMutation.domain.map fun input => {
        connective := input.connective
        left := input.left
        right := input.right
        verdict := algebraMutation.evaluate input.connective input.left input.right }

def expectedMutationCaseResults (mutation : MutationDescriptor) : List CaseResult :=
  expectedCaseResults mutation

def expectedMutationAlgebraResults (mutation : MutationDescriptor) : List AlgebraResult :=
  expectedAlgebraResults mutation

private def validateCommandLogs (commands : List CommandRecord) (logs : List FileDigest)
    (context : String) : Except String Unit := do
  if commands.isEmpty then throw s!"{context}: commands must not be empty"
  match firstDuplicate? (commands.map (·.id)) with
  | some duplicate => throw s!"{context}: duplicate command id '{duplicate}'"
  | none => pure ()
  let referenced := commands.flatMap fun command =>
    [command.stdoutLog.toString, command.stderrLog.toString]
  match firstDuplicate? referenced with
  | some duplicate => throw s!"{context}: command log path '{duplicate}' is reused"
  | none => pure ()
  let recorded := logs.map (·.path.toString)
  if recorded != referenced then
    throw s!"{context}: raw logs must match command stdout/stderr paths in exact order"

private def validateGate (gate : GateRecord) (baseline : List FileDigest)
    (context : String) : Except String Unit := do
  if gate.outcome != .passed then throw s!"{context}: gate did not pass"
  validateCommandLogs gate.commands gate.rawLogs context
  if gate.commands.any (·.exitStatus != 0) then
    throw s!"{context}: a passed gate contains a failing command"
  if gate.sourceFiles != baseline then
    throw s!"{context}: source inventory differs from the packet-pinned baseline"

private def validateToolchain (actual expected : List ToolchainRecord) : Except String Unit := do
  if expected.isEmpty then throw "qualification packet: toolchain must not be empty"
  match firstDuplicate? (expected.map (·.name)) with
  | some duplicate => throw s!"qualification packet: duplicate toolchain '{duplicate}'"
  | none => pure ()
  if !(expected.map (·.name)).contains "rustc" ||
      !(expected.map (·.name)).contains "cargo" then
    throw "qualification packet: toolchain must record rustc and cargo"
  if actual != expected then
    throw "qualification result: toolchain identity differs from the packet"

private def validateMutation (record : MutationRecord) (mutation : MutationDescriptor)
    (patch : FileDigest) (baseline : List FileDigest) : Except String Unit := do
  let context := s!"mutation exercise {mutation.mechanism.exercise}"
  if record.exercise != mutation.mechanism.exercise then
    throw s!"{context}: record exercise is {record.exercise}"
  if record.mutationId != mutation.mechanism.tag then
    throw s!"{context}: mutation id '{record.mutationId}' does not match '{mutation.mechanism.tag}'"
  if !record.predictionAttestedBeforePatch then
    throw s!"{context}: prediction was not attested before patching"
  if record.patch != patch.path || record.patchSha256 != patch.sha256 then
    throw s!"{context}: patch does not match the packet"
  validateCommandLogs record.commands record.rawLogs context
  if record.exitStatuses != record.commands.map (·.exitStatus) then
    throw s!"{context}: exitStatuses must match embedded command statuses in exact order"
  if record.observedCaseResults != expectedCaseResults mutation then
    throw s!"{context}: complete ordered case results differ from the typed mutation plan"
  if record.observedAlgebraResults != expectedAlgebraResults mutation then
    throw s!"{context}: complete ordered algebra results differ from the typed mutation plan"
  if !record.unexpectedDifferences.isEmpty then
    throw s!"{context}: record contains unexpected differences"
  if record.outcome != .matchedPrediction then
    throw s!"{context}: outcome is not matchedPrediction"
  if record.restoration.outcome != .passed then
    throw s!"{context}: restoration did not pass"
  if !record.restoration.reversePatchApplied then
    throw s!"{context}: reverse patch was not recorded as applied"
  if record.restoredSourceFiles != baseline then
    throw s!"{context}: restored source inventory differs from the packet-pinned baseline"

def Result.validateMetadata (result : Result) (expected : ExpectedPacket) : Except String Unit := do
  if result.schemaVersion != resultSchemaVersion then
    throw s!"qualification result: unsupported schema version {result.schemaVersion}"
  if result.packetId != expected.packetId then
    throw "qualification result: packet id mismatch"
  if result.packetIndexSha256 != expected.packetIndexSha256 then
    throw "qualification result: packet-index digest mismatch"
  if result.sourceRevision != expected.sourceRevision then
    throw "qualification result: source-project revision mismatch"
  if result.candidateBaseRevision != expected.candidateBaseRevision then
    throw "qualification result: candidate base revision mismatch"
  if result.assuranceClass != expected.assuranceClass then
    throw "qualification result: assurance class differs from the expected workflow"
  if result.isolationBoundary != expected.isolationBoundary then
    throw "qualification result: isolation boundary mismatch"
  if !result.unresolvedQuestions.isEmpty then
    throw "qualification result: unresolved questions must be empty for a passing record"
  if result.mutationPlanId != mutationPlan.id then
    throw s!"qualification result: mutation plan '{result.mutationPlanId}' does not match '{mutationPlan.id}'"
  if result.mutationPlanSha256 != expected.mutationPlanSha256 then
    throw "qualification result: mutation-plan digest mismatch"
  if result.capabilityId != capability.id then
    throw s!"qualification result: capability '{result.capabilityId}' does not match '{capability.id}'"
  if result.baselineImplementationRevision != expected.baselineImplementationRevision then
    throw "qualification result: baseline implementation revision mismatch"
  if result.baselineSourceFiles != expected.baselineSourceFiles then
    throw "qualification result: baseline source inventory mismatch"
  validateToolchain result.toolchain expected.toolchain
  validateGate result.naturalGate expected.baselineSourceFiles "natural gate"
  validateGate result.finalRestorationGate expected.baselineSourceFiles "final restoration gate"
  if result.mutations.length != mutationPlan.mutations.length then
    throw s!"qualification result: expected {mutationPlan.mutations.length} mutation records, found {result.mutations.length}"
  if expected.patches.length != mutationPlan.mutations.length then
    throw "qualification packet: patch inventory does not match the mutation plan"
  for ((record, mutation), patch) in
      (result.mutations.zip mutationPlan.mutations).zip expected.patches do
    validateMutation record mutation patch expected.baselineSourceFiles

end A12Kernel.Qualification.MutationResult
