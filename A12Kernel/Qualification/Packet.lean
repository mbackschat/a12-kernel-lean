import A12Kernel.Evidence.FlatProtocolBridge
import A12Kernel.Process.Artifact
import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! # Mutation qualification packet contract

This pure module defines the closed, language-neutral packet index used to qualify the frozen
Rust implementation of `flat-validation-empty-logic-v1`. Packet assembly and filesystem checks
live at the IO boundary; this module owns only identities, structure, codecs, and invariants.
-/

namespace A12Kernel.Qualification.Packet

open Lean
open A12Kernel.Evidence.FlatProtocolBridge
open A12Kernel.Process.Artifact

def packetSchemaVersion : Nat := 2

def packetId : String :=
  "flat-validation-empty-logic-v1-rust-mutation-qualification-v1"

def baselineImplementationRevision : String :=
  "7606fd5b881a8bdb8c94daf409ff4c495e572b29"

def observerCandidatePathText : String := "src/bin/qualification-observer.rs"

def sourceProjectName : String := "a12-kernel-lean"

def executionProfileId : String := "macos-homebrew-rust-v1"

def candidateWorkingDirectory : String := "candidateRoot"

def disposableIsolationBoundary : String := "disposablePacketBaselineCopy"

def toolchainPathEntries : List String :=
  ["/opt/homebrew/opt/rustup/bin", "/opt/homebrew/bin", "/usr/bin", "/bin"]

structure Compatibility where
  referenceSemanticsVersion : String
  protocolVersion : Nat
  manifestSchemaVersion : Nat
  kernelBehaviorVersion : String
  operation : String
  deriving Repr, DecidableEq

structure SourceFile where
  candidatePath : PortablePath
  packetPath : PortablePath
  sha256 : Digest
  executable : Bool
  deriving Repr, DecidableEq

structure ToolchainSpec where
  name : String
  version : String
  deriving Repr, DecidableEq

structure ExecutionProfile where
  id : String
  workingDirectory : String
  pathEntries : List String
  isolationBoundary : String
  deriving Repr, DecidableEq

structure CommandSpec where
  id : String
  argv : List String
  expectedExitStatus : Nat
  deriving Repr, DecidableEq

structure MutationArtifact where
  exercise : Nat
  mutationId : String
  patch : FileDigest
  expectedObservation : FileDigest
  mutatedSourceFiles : List FileDigest
  commands : List CommandSpec
  deriving Repr, DecidableEq

structure Index where
  schemaVersion : Nat
  id : String
  sourceRevision : String
  candidateBaseRevision : String
  compatibility : Compatibility
  executionProfile : ExecutionProfile
  mutationPlan : FileDigest
  baselineRevision : String
  baselineSourceFiles : List SourceFile
  observer : FileDigest
  baselineObserverPatch : FileDigest
  expectedBaselineObservation : FileDigest
  instrumentedBaselineSourceFiles : List FileDigest
  toolchain : List ToolchainSpec
  naturalGateCommands : List CommandSpec
  mutations : List MutationArtifact
  finalRestorationGateCommands : List CommandSpec
  auxiliaryFiles : List FileDigest
  payloadFiles : List FileDigest
  deriving Repr, DecidableEq

def expectedCompatibility : Compatibility := {
  referenceSemanticsVersion := capability.referenceSemanticsVersion
  protocolVersion := capability.protocolVersion
  manifestSchemaVersion := capability.manifestSchemaVersion
  kernelBehaviorVersion := capability.kernelBehaviorVersion
  operation := capability.operation }

def expectedExecutionProfile : ExecutionProfile := {
  id := executionProfileId
  workingDirectory := candidateWorkingDirectory
  pathEntries := toolchainPathEntries
  isolationBoundary := disposableIsolationBoundary }

def mutationFileStem (mutation : MutationDescriptor) : String :=
  let exercise := mutation.mechanism.exercise
  let number := if exercise < 10 then s!"0{exercise}" else toString exercise
  s!"{number}-{mutation.mechanism.tag}"

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

private def nonempty (value context : String) : Except String String := do
  if value.isEmpty then throw s!"{context}: must not be empty"
  pure value

private def isLowerHex (character : Char) : Bool :=
  decide ('0' ≤ character && character ≤ '9') ||
    decide ('a' ≤ character && character ≤ 'f')

private def gitRevision (value context : String) : Except String String := do
  if value.length != 40 || !value.toList.all isLowerHex then
    throw s!"{context}: expected a 40-character lowercase hexadecimal Git revision"
  pure value

private def parsePortablePath (value context : String) : Except String PortablePath :=
  match PortablePath.parse value with
  | .ok path => pure path
  | .error error => throw s!"{context}: {error}"

private def parseDigest (value context : String) : Except String Digest :=
  match Digest.parse value with
  | .ok digest => pure digest
  | .error error => throw s!"{context}: {error}"

private def parseCompatibility (json : Json) : Except String Compatibility := do
  let context := "qualification packet compatibility"
  requireObject json ["capabilityId", "referenceSemanticsVersion", "protocolVersion",
    "manifestSchemaVersion", "kernelBehaviorVersion", "operation"] context
  let capabilityId : String ← required json "capabilityId" context
  if capabilityId != capability.id then
    throw s!"{context}: capability '{capabilityId}' does not match '{capability.id}'"
  pure {
    referenceSemanticsVersion := ← required json "referenceSemanticsVersion" context
    protocolVersion := ← required json "protocolVersion" context
    manifestSchemaVersion := ← required json "manifestSchemaVersion" context
    kernelBehaviorVersion := ← required json "kernelBehaviorVersion" context
    operation := ← required json "operation" context }

private def parseExecutionProfile (json : Json) : Except String ExecutionProfile := do
  let context := "qualification packet executionProfile"
  requireObject json ["id", "workingDirectory", "pathEntries", "isolationBoundary"] context
  let pathEntries : List String ← required json "pathEntries" context
  if pathEntries.isEmpty || pathEntries.any (·.isEmpty) then
    throw s!"{context}: pathEntries must contain only nonempty paths"
  pure {
    id := ← nonempty (← required json "id" context) s!"{context} id"
    workingDirectory := ← nonempty (← required json "workingDirectory" context)
      s!"{context} workingDirectory"
    pathEntries
    isolationBoundary := ← nonempty (← required json "isolationBoundary" context)
      s!"{context} isolationBoundary" }

private def parseSourceFile (json : Json) (index : Nat) : Except String SourceFile := do
  let context := s!"qualification packet baselineSourceFiles[{index}]"
  requireObject json ["candidatePath", "packetPath", "sha256", "executable"] context
  pure {
    candidatePath := ← parsePortablePath (← required json "candidatePath" context)
      s!"{context} candidatePath"
    packetPath := ← parsePortablePath (← required json "packetPath" context)
      s!"{context} packetPath"
    sha256 := ← parseDigest (← required json "sha256" context) s!"{context} sha256"
    executable := ← required json "executable" context }

private def parseToolchain (json : Json) (index : Nat) : Except String ToolchainSpec := do
  let context := s!"qualification packet toolchain[{index}]"
  requireObject json ["name", "version"] context
  pure {
    name := ← nonempty (← required json "name" context) s!"{context} name"
    version := ← nonempty (← required json "version" context) s!"{context} version" }

private def parseCommand (json : Json) (context : String) : Except String CommandSpec := do
  requireObject json ["id", "argv", "expectedExitStatus"] context
  let argv : List String ← required json "argv" context
  if argv.isEmpty || argv.any (·.isEmpty) then
    throw s!"{context}: argv must contain only nonempty arguments"
  pure {
    id := ← nonempty (← required json "id" context) s!"{context} id"
    argv
    expectedExitStatus := ← required json "expectedExitStatus" context }

private def parseCommands (json : Json) (name context : String) : Except String (List CommandSpec) := do
  let values : List Json ← required json name context
  if values.isEmpty then throw s!"{context}: {name} must not be empty"
  values.zipIdx.mapM fun (value, index) => parseCommand value s!"{context} {name}[{index}]"

private def parseFileDigestArray (json : Json) (name context : String) :
    Except String (List FileDigest) := do
  let values : List Json ← required json name context
  let files ← values.zipIdx.mapM fun (value, index) =>
    FileDigest.parseJson value s!"{context} {name}[{index}]"
  FileDigest.validateInventory files
  pure files

private def parseMutation (json : Json) (index : Nat) : Except String MutationArtifact := do
  let context := s!"qualification packet mutations[{index}]"
  requireObject json ["exercise", "mutationId", "patch", "expectedObservation",
    "mutatedSourceFiles", "commands"] context
  let mutatedSourceFiles ← parseFileDigestArray json "mutatedSourceFiles" context
  pure {
    exercise := ← required json "exercise" context
    mutationId := ← nonempty (← required json "mutationId" context) s!"{context} mutationId"
    patch := ← FileDigest.parseJson (← requiredJson json "patch" context) s!"{context} patch"
    expectedObservation := ← FileDigest.parseJson
      (← requiredJson json "expectedObservation" context) s!"{context} expectedObservation"
    mutatedSourceFiles
    commands := ← parseCommands json "commands" context }

def Compatibility.asJson (value : Compatibility) : Json :=
  Json.mkObj [
    ("capabilityId", toJson capability.id),
    ("referenceSemanticsVersion", toJson value.referenceSemanticsVersion),
    ("protocolVersion", toJson value.protocolVersion),
    ("manifestSchemaVersion", toJson value.manifestSchemaVersion),
    ("kernelBehaviorVersion", toJson value.kernelBehaviorVersion),
    ("operation", toJson value.operation)]

def SourceFile.asJson (file : SourceFile) : Json :=
  Json.mkObj [
    ("candidatePath", file.candidatePath.asJson),
    ("packetPath", file.packetPath.asJson),
    ("sha256", file.sha256.asJson),
    ("executable", toJson file.executable)]

def ToolchainSpec.asJson (toolchain : ToolchainSpec) : Json :=
  Json.mkObj [("name", toJson toolchain.name), ("version", toJson toolchain.version)]

def ExecutionProfile.asJson (profile : ExecutionProfile) : Json :=
  Json.mkObj [
    ("id", toJson profile.id),
    ("workingDirectory", toJson profile.workingDirectory),
    ("pathEntries", toJson profile.pathEntries),
    ("isolationBoundary", toJson profile.isolationBoundary)]

def CommandSpec.asJson (command : CommandSpec) : Json :=
  Json.mkObj [
    ("id", toJson command.id),
    ("argv", toJson command.argv),
    ("expectedExitStatus", toJson command.expectedExitStatus)]

def MutationArtifact.asJson (mutation : MutationArtifact) : Json :=
  Json.mkObj [
    ("exercise", toJson mutation.exercise),
    ("mutationId", toJson mutation.mutationId),
    ("patch", mutation.patch.asJson),
    ("expectedObservation", mutation.expectedObservation.asJson),
    ("mutatedSourceFiles", Json.arr (mutation.mutatedSourceFiles.map FileDigest.asJson).toArray),
    ("commands", Json.arr (mutation.commands.map CommandSpec.asJson).toArray)]

def Index.asJson (index : Index) : Json :=
  Json.mkObj [
    ("packetSchemaVersion", toJson index.schemaVersion),
    ("packetId", toJson index.id),
    ("sourceProject", toJson sourceProjectName),
    ("sourceRevision", toJson index.sourceRevision),
    ("candidateBaseRevision", toJson index.candidateBaseRevision),
    ("compatibility", index.compatibility.asJson),
    ("executionProfile", index.executionProfile.asJson),
    ("mutationPlan", index.mutationPlan.asJson),
    ("baselineImplementationRevision", toJson index.baselineRevision),
    ("baselineSourceFiles", Json.arr (index.baselineSourceFiles.map SourceFile.asJson).toArray),
    ("observer", index.observer.asJson),
    ("baselineObserverPatch", index.baselineObserverPatch.asJson),
    ("expectedBaselineObservation", index.expectedBaselineObservation.asJson),
    ("instrumentedBaselineSourceFiles",
      Json.arr (index.instrumentedBaselineSourceFiles.map FileDigest.asJson).toArray),
    ("toolchain", Json.arr (index.toolchain.map ToolchainSpec.asJson).toArray),
    ("naturalGateCommands", Json.arr (index.naturalGateCommands.map CommandSpec.asJson).toArray),
    ("mutations", Json.arr (index.mutations.map MutationArtifact.asJson).toArray),
    ("finalRestorationGateCommands",
      Json.arr (index.finalRestorationGateCommands.map CommandSpec.asJson).toArray),
    ("auxiliaryFiles", Json.arr (index.auxiliaryFiles.map FileDigest.asJson).toArray),
    ("payloadFiles", Json.arr (index.payloadFiles.map FileDigest.asJson).toArray)]

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest => if rest.contains value then some value else firstDuplicate? rest

private def validateCommands (commands : List CommandSpec) (context : String) : Except String Unit := do
  if commands.isEmpty then throw s!"{context}: commands must not be empty"
  match firstDuplicate? (commands.map (·.id)) with
  | some duplicate => throw s!"{context}: duplicate command id '{duplicate}'"
  | none => pure ()
  if commands.any fun command => command.argv.isEmpty || command.argv.any (·.isEmpty) then
    throw s!"{context}: every command needs nonempty argv"

private def sourceDigest (file : SourceFile) : FileDigest := {
  path := file.candidatePath
  sha256 := file.sha256 }

def Index.baselineResultFiles (index : Index) : List FileDigest :=
  index.baselineSourceFiles.map sourceDigest

private def referencedPayloadFiles (index : Index) : List FileDigest :=
  let sourceFiles := index.baselineSourceFiles.map fun file => {
    path := file.packetPath
    sha256 := file.sha256 }
  [index.mutationPlan, index.observer, index.baselineObserverPatch,
      index.expectedBaselineObservation] ++ sourceFiles ++
    index.mutations.flatMap (fun mutation => [mutation.patch, mutation.expectedObservation]) ++
    index.auxiliaryFiles

def Index.validate (index : Index) : Except String Unit := do
  if index.schemaVersion != packetSchemaVersion then
    throw s!"qualification packet: unsupported schema version {index.schemaVersion}"
  if index.id != packetId then
    throw s!"qualification packet: packet id '{index.id}' does not match '{packetId}'"
  let _ ← gitRevision index.sourceRevision "qualification packet sourceRevision"
  let _ ← gitRevision index.candidateBaseRevision "qualification packet candidateBaseRevision"
  if index.compatibility != expectedCompatibility then
    throw "qualification packet: compatibility identity differs from the typed capability"
  if index.executionProfile != expectedExecutionProfile then
    throw "qualification packet: execution profile differs from the source-owned profile"
  if index.baselineRevision != baselineImplementationRevision then
    throw "qualification packet: baseline implementation revision mismatch"
  let rolePath (value : String) : Except String PortablePath := PortablePath.parse value
  if index.mutationPlan.path != (← rolePath
      "reference/flat-validation-empty-logic-v1.mutation-plan.json") then
    throw "qualification packet: mutation plan uses the wrong role path"
  if index.observer.path != (← rolePath "assets/flat_validation_observer.rs") then
    throw "qualification packet: observer uses the wrong role path"
  if index.baselineObserverPatch.path != (← rolePath "patches/00-observer.patch") then
    throw "qualification packet: baseline observer patch uses the wrong role path"
  if index.expectedBaselineObservation.path !=
      (← rolePath "expected/00-baseline.observation.json") then
    throw "qualification packet: baseline observation uses the wrong role path"
  if index.baselineSourceFiles.isEmpty then
    throw "qualification packet: baseline source inventory must not be empty"
  validatePathSet (index.baselineSourceFiles.map (·.candidatePath))
  validatePathSet (index.baselineSourceFiles.map (·.packetPath))
  for source in index.baselineSourceFiles do
    if source.packetPath != (← rolePath s!"baseline/{source.candidatePath}") then
      throw s!"qualification packet: baseline source '{source.candidatePath}' uses the wrong packet path"
  if index.baselineSourceFiles.map (·.candidatePath.toString) !=
      (index.baselineSourceFiles.map (·.candidatePath.toString)).mergeSort then
    throw "qualification packet: baseline source files must be in lexical candidate-path order"
  FileDigest.validateInventory index.instrumentedBaselineSourceFiles
  let observerCandidatePath ← match PortablePath.parse observerCandidatePathText with
    | .ok path => pure path
    | .error error => throw s!"qualification packet: invalid observer path: {error}"
  let instrumentedObserver : FileDigest := {
    path := observerCandidatePath
    sha256 := index.observer.sha256 }
  let expectedInstrumented :=
    (index.baselineResultFiles ++ [instrumentedObserver]).mergeSort fun left right =>
        left.path.toString ≤ right.path.toString
  if index.instrumentedBaselineSourceFiles != expectedInstrumented then
    throw "qualification packet: instrumented baseline must add only the pinned observer"
  if index.toolchain.length != 2 || index.toolchain.map (·.name) != ["rustc", "cargo"] then
    throw "qualification packet: toolchain must record rustc then cargo"
  if index.toolchain.any (·.version.isEmpty) then
    throw "qualification packet: toolchain versions must not be empty"
  validateCommands index.naturalGateCommands "qualification packet natural gate"
  validateCommands index.finalRestorationGateCommands
    "qualification packet final restoration gate"
  if index.mutations.length != A12Kernel.Evidence.FlatProtocolBridge.mutationPlan.mutations.length then
    throw s!"qualification packet: expected {A12Kernel.Evidence.FlatProtocolBridge.mutationPlan.mutations.length} mutations, found {index.mutations.length}"
  for (artifact, descriptor) in
      index.mutations.zip A12Kernel.Evidence.FlatProtocolBridge.mutationPlan.mutations do
    let context := s!"qualification packet mutation exercise {descriptor.mechanism.exercise}"
    if artifact.exercise != descriptor.mechanism.exercise then
      throw s!"{context}: exercise is {artifact.exercise}"
    if artifact.mutationId != descriptor.mechanism.tag then
      throw s!"{context}: mutation id '{artifact.mutationId}' does not match '{descriptor.mechanism.tag}'"
    let stem := mutationFileStem descriptor
    if artifact.patch.path != (← rolePath s!"patches/{stem}.patch") then
      throw s!"{context}: patch uses the wrong role path"
    if artifact.expectedObservation.path !=
        (← rolePath s!"expected/{stem}.observation.json") then
      throw s!"{context}: expected observation uses the wrong role path"
    FileDigest.validateInventory artifact.mutatedSourceFiles
    if !(artifact.mutatedSourceFiles.map (·.path.toString)).contains observerCandidatePathText then
      throw s!"{context}: mutated source inventory is missing the observer"
    validateCommands artifact.commands context
  FileDigest.validateInventory index.auxiliaryFiles
  FileDigest.validateInventory index.payloadFiles
  let referenced := referencedPayloadFiles index
  FileDigest.validateInventory referenced
  if index.payloadFiles != referenced then
    throw "qualification packet: payloadFiles must equal all role-bearing payloads in exact order"

def parseJson (json : Json) : Except String Index := do
  let context := "mutation qualification packet"
  requireObject json ["packetSchemaVersion", "packetId", "sourceProject", "sourceRevision",
    "candidateBaseRevision", "compatibility", "executionProfile", "mutationPlan",
    "baselineImplementationRevision", "baselineSourceFiles", "observer",
    "baselineObserverPatch", "expectedBaselineObservation", "instrumentedBaselineSourceFiles",
    "toolchain", "naturalGateCommands", "mutations", "finalRestorationGateCommands",
    "auxiliaryFiles", "payloadFiles"] context
  let sourceJson : List Json ← required json "baselineSourceFiles" context
  let toolchainJson : List Json ← required json "toolchain" context
  let mutationJson : List Json ← required json "mutations" context
  let sourceProject : String ← required json "sourceProject" context
  if sourceProject != sourceProjectName then
    throw s!"{context}: sourceProject '{sourceProject}' does not match '{sourceProjectName}'"
  let index : Index := {
    schemaVersion := ← required json "packetSchemaVersion" context
    id := ← nonempty (← required json "packetId" context) s!"{context} packetId"
    sourceRevision := ← gitRevision (← required json "sourceRevision" context)
      s!"{context} sourceRevision"
    candidateBaseRevision := ← gitRevision (← required json "candidateBaseRevision" context)
      s!"{context} candidateBaseRevision"
    compatibility := ← parseCompatibility (← requiredJson json "compatibility" context)
    executionProfile := ← parseExecutionProfile (← requiredJson json "executionProfile" context)
    mutationPlan := ← FileDigest.parseJson (← requiredJson json "mutationPlan" context)
      s!"{context} mutationPlan"
    baselineRevision := ← nonempty (← required json "baselineImplementationRevision" context)
      s!"{context} baselineImplementationRevision"
    baselineSourceFiles := ← sourceJson.zipIdx.mapM fun (value, index) =>
      parseSourceFile value index
    observer := ← FileDigest.parseJson (← requiredJson json "observer" context)
      s!"{context} observer"
    baselineObserverPatch := ← FileDigest.parseJson
      (← requiredJson json "baselineObserverPatch" context)
      s!"{context} baselineObserverPatch"
    expectedBaselineObservation := ← FileDigest.parseJson
      (← requiredJson json "expectedBaselineObservation" context)
      s!"{context} expectedBaselineObservation"
    instrumentedBaselineSourceFiles :=
      ← parseFileDigestArray json "instrumentedBaselineSourceFiles" context
    toolchain := ← toolchainJson.zipIdx.mapM fun (value, index) =>
      parseToolchain value index
    naturalGateCommands := ← parseCommands json "naturalGateCommands" context
    mutations := ← mutationJson.zipIdx.mapM fun (value, index) => parseMutation value index
    finalRestorationGateCommands := ← parseCommands json "finalRestorationGateCommands" context
    auxiliaryFiles := ← parseFileDigestArray json "auxiliaryFiles" context
    payloadFiles := ← parseFileDigestArray json "payloadFiles" context }
  index.validate
  pure index

def parseText (input : String) : Except String Index := do
  let json ← match A12Kernel.Reference.StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"invalid strict qualification-packet JSON: {repr error}"
  parseJson json

end A12Kernel.Qualification.Packet
