import A12Kernel.Qualification.Checker

/-! # Source-executed mutation qualification replay

This IO-only runner executes the packet-owned command policy in a disposable baseline copy, captures every process stream, checks the natural path-and-byte inventory after each mutation, and emits a result record for the strict checker. It establishes that the generated packet is executable on the source maintainer's machine; a separately returned consumer record remains an isolated-session attestation.
-/

namespace A12Kernel.Qualification.Runner

open Lean
open A12Kernel.Evidence.FlatProtocolBridge
open A12Kernel.Qualification.Artifact
open A12Kernel.Qualification.Packet

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private structure RecordedCommand where
  record : MutationResult.CommandRecord
  logs : List FileDigest

private def parsePath (value context : String) : IO PortablePath :=
  match PortablePath.parse value with
  | .ok path => pure path
  | .error error => fail s!"{context}: {error}"

private def parseDigest (value context : String) : IO Digest :=
  match Digest.parse value with
  | .ok digest => pure digest
  | .error error => fail s!"{context}: {error}"

private def writeLog (resultRoot : System.FilePath) (relative content : String) : IO FileDigest := do
  let pathId ← parsePath relative s!"invalid qualification log path '{relative}'"
  let path := resultRoot / relative
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path content
  pure {
    path := pathId
    sha256 := ← parseDigest (← A12Kernel.Process.Sha256.file path)
      s!"invalid qualification log digest for '{relative}'" }

private def runCommand (candidateRoot resultRoot : System.FilePath)
    (profile : ExecutionProfile) (phase : String) (spec : CommandSpec) : IO RecordedCommand := do
  let (command, arguments) ← match spec.argv with
    | command :: arguments => pure (command, arguments)
    | [] => fail s!"qualification command '{spec.id}' has empty argv"
  let output ← IO.Process.output {
    cmd := command
    args := arguments.toArray
    cwd := some candidateRoot
    env := #[("PATH", some (String.intercalate ":" profile.pathEntries))] }
  let stdoutLog ← writeLog resultRoot s!"logs/{phase}/{spec.id}.stdout" output.stdout
  let stderrLog ← writeLog resultRoot s!"logs/{phase}/{spec.id}.stderr" output.stderr
  let exitStatus := output.exitCode.toNat
  let record : MutationResult.CommandRecord := {
    id := spec.id
    argv := spec.argv
    exitStatus
    stdoutLog := stdoutLog.path
    stderrLog := stderrLog.path }
  if exitStatus != spec.expectedExitStatus then
    fail s!"qualification command '{spec.id}' exited {exitStatus}, expected {spec.expectedExitStatus}"
  pure { record, logs := [stdoutLog, stderrLog] }

private def runCommands (candidateRoot resultRoot : System.FilePath) (phase : String)
    (profile : ExecutionProfile) (commands : List CommandSpec) :
    IO (List MutationResult.CommandRecord × List FileDigest) := do
  let recorded ← commands.mapM (runCommand candidateRoot resultRoot profile phase)
  pure (recorded.map (·.record), recorded.flatMap (·.logs))

private def packetDigest (packetIndexPath : System.FilePath) : IO Digest := do
  parseDigest (← A12Kernel.Process.Sha256.file packetIndexPath)
    "invalid qualification packet-index digest"

private def capturedObservation (resultRoot : System.FilePath)
    (commands : List MutationResult.CommandRecord) (commandId : String)
    (expectedExercise : Nat) : IO MutationResult.Observation := do
  let command ← match commands.filter (·.id == commandId) with
    | [command] => pure command
    | [] => fail s!"qualification replay is missing observer command '{commandId}'"
    | _ => fail s!"qualification replay contains duplicate observer command '{commandId}'"
  let input ← IO.FS.readFile (resultRoot / command.stdoutLog.toString)
  let observation ← MutationResult.parseObservationText input |> IO.ofExcept
  if observation.exercise != expectedExercise then
    fail s!"qualification observer exercise {observation.exercise} does not match {expectedExercise}"
  pure observation

/-- Execute the natural gate, all seven single mutations, and the final restoration gate in a disposable candidate copy, then require the strict checker to accept the captured source replay. -/
def run (packetIndexPath resultRoot : System.FilePath) (index : Index) :
    IO MutationResult.Result := do
  let packetRoot ← match packetIndexPath.parent with
    | some parent => pure parent
    | none => fail "qualification packet index has no parent directory"
  let workspace ← match packetRoot.parent with
    | some parent => pure parent
    | none => fail "qualification packet root has no workspace parent"
  let candidateRoot := workspace / "candidate"
  if ← System.FilePath.pathExists candidateRoot then
    fail s!"qualification replay candidate already exists: '{candidateRoot}'"
  if ← System.FilePath.pathExists resultRoot then
    fail s!"qualification replay result already exists: '{resultRoot}'"
  Checker.copyBaseline packetRoot candidateRoot index
  IO.FS.createDirAll resultRoot
  try
    let baseline := index.baselineResultFiles
    if (← Checker.candidateInventory candidateRoot) != baseline then
      fail "qualification replay copied baseline differs from the packet inventory"

    let (naturalCommands, naturalLogs) ← runCommands candidateRoot resultRoot "natural"
      index.executionProfile index.naturalGateCommands
    let _ ← capturedObservation resultRoot naturalCommands "observe-baseline" 0
    let naturalFiles ← Checker.candidateInventory candidateRoot
    if naturalFiles != baseline then
      fail "qualification replay natural gate did not restore the baseline"
    let naturalGate : MutationResult.GateRecord := {
      outcome := .passed
      commands := naturalCommands
      rawLogs := naturalLogs
      sourceFiles := naturalFiles }

    let mut mutationRecords : List MutationResult.MutationRecord := []
    for artifact in index.mutations do
      let predictionAttestedBeforePatch := true
      let phase := s!"mutation-{artifact.exercise}"
      let (commands, logs) ← runCommands candidateRoot resultRoot phase
        index.executionProfile artifact.commands
      let observation ← capturedObservation resultRoot commands "observe" artifact.exercise
      let restoredFiles ← Checker.candidateInventory candidateRoot
      if restoredFiles != baseline then
        fail s!"qualification replay mutation {artifact.exercise} did not restore the baseline"
      mutationRecords := mutationRecords ++ [{
        exercise := artifact.exercise
        mutationId := artifact.mutationId
        predictionAttestedBeforePatch
        patch := artifact.patch.path
        patchSha256 := artifact.patch.sha256
        commands
        rawLogs := logs
        exitStatuses := commands.map (·.exitStatus)
        observedCaseResults := observation.caseResults
        observedAlgebraResults := observation.algebraResults
        unexpectedDifferences := []
        outcome := .matchedPrediction
        restoration := { outcome := .passed, reversePatchApplied := true }
        restoredSourceFiles := restoredFiles }]

    let (finalCommands, finalLogs) ← runCommands candidateRoot resultRoot "final"
      index.executionProfile index.finalRestorationGateCommands
    let finalFiles ← Checker.candidateInventory candidateRoot
    if finalFiles != baseline then
      fail "qualification replay final gate did not preserve the baseline"
    let finalGate : MutationResult.GateRecord := {
      outcome := .passed
      commands := finalCommands
      rawLogs := finalLogs
      sourceFiles := finalFiles }

    let result : MutationResult.Result := {
      schemaVersion := MutationResult.resultSchemaVersion
      packetId := index.id
      packetIndexSha256 := ← packetDigest packetIndexPath
      sourceRevision := index.sourceRevision
      candidateBaseRevision := index.candidateBaseRevision
      assuranceClass := .sourceExecutedReplay
      isolationBoundary := index.executionProfile.isolationBoundary
      unresolvedQuestions := []
      mutationPlanId := mutationPlan.id
      mutationPlanSha256 := index.mutationPlan.sha256
      capabilityId := capability.id
      baselineImplementationRevision := index.baselineRevision
      baselineSourceFiles := baseline
      toolchain := index.toolchain.map fun toolchain => {
        name := toolchain.name, version := toolchain.version }
      naturalGate
      mutations := mutationRecords
      finalRestorationGate := finalGate }
    IO.FS.writeFile (resultRoot / "RESULT.json") (result.asJson.pretty 100 ++ "\n")
    Checker.checkResult packetIndexPath (resultRoot / "RESULT.json") index .sourceExecutedReplay
    pure result
  finally
    if ← System.FilePath.pathExists candidateRoot then IO.FS.removeDirAll candidateRoot

end A12Kernel.Qualification.Runner
