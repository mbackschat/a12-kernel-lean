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
  let observation ← orThrow case.id (Observation.fromJson (← readJson (root / case.caseRef)))
  if observation.id != case.id then
    throw (IO.userError s!"{case.id}: external id is '{observation.id}'")
  if observation.kernelVersion != bundle.kernelVersion then
    throw (IO.userError s!"{case.id}: external kernel version is {observation.kernelVersion}")
  if !observation.divergences.isEmpty then
    throw (IO.userError s!"{case.id}: external capture records a kernel-strategy divergence")
  if !safeRelative observation.modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{observation.modelRef}'")
  if !(← System.FilePath.pathExists (root / observation.modelRef)) then
    throw (IO.userError s!"{case.id}: missing retained model '{observation.modelRef}'")
  let observed := observation.expected.filter (·.startsWith s!"{case.focusCode}|")
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
