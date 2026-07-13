import A12Kernel.Evidence.Replay
import Lean.Data.Json

/-! IO-only retained-kernel-evidence replay. This module is an executable boundary and
is intentionally absent from the library, conformance, and trusted theorem roots. -/

open Lean
open A12Kernel
open A12Kernel.Evidence

private structure Observation where
  id : String
  kernelVersion : String
  modelRef : String
  expected : List String
  divergences : List Json

private structure DiagnosticObservation where
  id : String
  kernelVersion : String
  modelRef : String
  expectedCode : String
  diagnosticCodes : List String

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def optionalArray (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure []

private def Observation.fromJson (json : Json) : Except String Observation := do
  let metadata ← json.getObjVal? "meta"
  let operation ← json.getObjVal? "op"
  let operationKind : String ← member operation "kind"
  if operationKind != "validateFull" then
    throw s!"unsupported external operation '{operationKind}'"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    modelRef := ← member json "modelRef"
    expected := ← member json "expected"
    divergences := ← optionalArray json "divergences" }

private def DiagnosticObservation.fromJson (json : Json) : Except String DiagnosticObservation := do
  let metadata ← json.getObjVal? "meta"
  let diagnostics : List Json ← member json "diagnostics"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    modelRef := ← member json "modelRef"
    expectedCode := ← member json "expectedCode"
    diagnosticCodes := ← diagnostics.mapM fun diagnostic => member diagnostic "code" }

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{context}: {message}")

private def readJson (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  orThrow path.toString (Json.parse content)

private def safeRelative (reference : String) : Bool :=
  !reference.isEmpty && !reference.startsWith "/" && !(reference.splitOn "/").contains ".."

private def checkCase (root : System.FilePath) (bundle : Bundle) (case : CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe caseRef '{case.caseRef}'")
  let json ← readJson (root / case.caseRef)
  let (externalId, externalVersion, modelRef, observed) ← match case.operation with
    | .resolve _ _ => do
        let observation ← orThrow case.id (DiagnosticObservation.fromJson json)
        if !(observation.diagnosticCodes.contains observation.expectedCode) then
          throw (IO.userError s!"{case.id}: expected diagnostic code is absent from retained diagnostics")
        pure (observation.id, observation.kernelVersion, observation.modelRef,
          [observation.expectedCode])
    | _ => do
        let observation ← orThrow case.id (Observation.fromJson json)
        if !observation.divergences.isEmpty then
          throw (IO.userError s!"{case.id}: external capture records a kernel-strategy divergence")
        pure (observation.id, observation.kernelVersion, observation.modelRef,
          observation.expected.filter (·.startsWith s!"{case.focusCode}|"))
  if externalId != case.id then
    throw (IO.userError s!"{case.id}: external id is '{externalId}'")
  if externalVersion != bundle.kernelVersion then
    throw (IO.userError s!"{case.id}: external kernel version is {externalVersion}")
  if !safeRelative modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{modelRef}'")
  if !(← System.FilePath.pathExists (root / modelRef)) then
    throw (IO.userError s!"{case.id}: missing retained model '{modelRef}'")
  let actual ← orThrow case.id case.replay
  if actual != observed then
    throw (IO.userError s!"{case.id}: observed {repr observed}, Lean produced {repr actual}")

def main : IO Unit := do
  let root : System.FilePath := "evidence/kernel-30.8.1"
  let bundle ← orThrow "projection.json"
    (Bundle.fromJson (← readJson (root / "projection.json")))
  orThrow "projection.json" bundle.validate
  for case in bundle.cases do
    checkCase root bundle case
  IO.println s!"kernel evidence: {bundle.cases.length}/{bundle.cases.length} projections agree ({bundle.kernelVersion})"
