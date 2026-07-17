import A12Kernel.Basic
import A12Kernel.Process.ArtifactTree
import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! # Compact semantic-observation bundles

This nontrusted reader owns only the operation-neutral contract between a certified evidence producer and typed Lean family projections. Raw capture verification remains a producer responsibility. The `qualification` member is always present on the wire; JSON `null` is its sole absent encoding.
-/

namespace A12Kernel.Evidence.ObservationBundle

open Lean
open A12Kernel.Process.Artifact

/-- Deliberate compact-export ceiling shared with the producer contract. -/
def maxBytes : Nat := 256 * 1024

structure QualificationIdentity where
  policyId : String
  receipt : FileDigest
  deriving Repr, BEq

structure SourceIdentity where
  producer : String
  revision : String
  rawCapture : FileDigest
  qualification : Option QualificationIdentity
  deriving Repr, BEq

structure ObservationCase where
  id : String
  input : Json
  observed : Json
  deriving BEq

structure Family where
  id : String
  projectionId : String
  projectionVersion : Nat
  source : SourceIdentity
  cases : List ObservationCase
  deriving BEq

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  families : List Family
  deriving BEq

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

private def adjacentDuplicate? (ordering : α → α → Ordering) : List α → Option α
  | [] => none
  | [_] => none
  | left :: right :: rest =>
      if ordering left right == .eq then some left
      else adjacentDuplicate? ordering (right :: rest)

private def firstDuplicate? (ordering : α → α → Ordering) (values : List α) : Option α :=
  adjacentDuplicate? ordering <| values.mergeSort fun left right => ordering left right != .gt

private def familyIdentityOrder (left right : Family) : Ordering :=
  match compare left.id right.id with
  | .eq =>
      match compare left.projectionId right.projectionId with
      | .eq => compare left.projectionVersion right.projectionVersion
      | order => order
  | order => order

private def parseQualification (json : Json) : Except String QualificationIdentity := do
  let context := "observation source qualification"
  requireObject json ["policyId", "receipt"] context
  pure {
    policyId := ← nonempty (← required json "policyId" context) "qualification policy id"
    receipt := ← FileDigest.parseJson (← requiredJson json "receipt" context)
      "qualification receipt" }

private def parseSource (json : Json) : Except String SourceIdentity := do
  let context := "observation source"
  requireObject json ["producer", "revision", "rawCapture", "qualification"] context
  let qualificationJson ← requiredJson json "qualification" context
  let qualification ← match qualificationJson with
    | .null => pure none
    | json => some <$> parseQualification json
  pure {
    producer := ← nonempty (← required json "producer" context) "source producer"
    revision := ← gitRevision (← required json "revision" context) "source Git revision"
    rawCapture := ← FileDigest.parseJson (← requiredJson json "rawCapture" context)
      "source raw capture"
    qualification }

private def parseCase (familyId : String) (json : Json) : Except String ObservationCase := do
  let context := s!"observation family '{familyId}' case"
  requireObject json ["id", "input", "observed"] context
  pure {
    id := ← nonempty (← required json "id" context) s!"{context} id"
    input := ← requiredJson json "input" context
    observed := ← requiredJson json "observed" context }

private def parseFamily (json : Json) : Except String Family := do
  let context := "observation family"
  requireObject json ["id", "projectionId", "projectionVersion", "source", "cases"] context
  let id ← nonempty (← required json "id" context) "family id"
  let projectionId ← nonempty (← required json "projectionId" context) "projection id"
  let projectionVersion : Nat ← required json "projectionVersion" context
  if projectionVersion == 0 then throw "projection version must be positive"
  let caseJson : List Json ← required json "cases" context
  if caseJson.isEmpty then throw s!"family '{id}' must contain at least one case"
  let cases ← caseJson.mapM (parseCase id)
  if let some duplicate := firstDuplicate? compare (cases.map (·.id)) then
    throw s!"family '{id}' has duplicate case id '{duplicate}'"
  pure {
    id
    projectionId
    projectionVersion
    source := ← parseSource (← requiredJson json "source" context)
    cases }

private def Bundle.fromJson (json : Json) : Except String Bundle := do
  let context := "observation bundle"
  requireObject json ["schemaVersion", "kernelVersion", "families"] context
  let schemaVersion : Nat ← required json "schemaVersion" context
  if schemaVersion != 1 then throw s!"unsupported observation-bundle schema version {schemaVersion}"
  let kernelVersion : String ← required json "kernelVersion" context
  if kernelVersion != A12Kernel.kernelVersion then
    throw s!"unsupported kernel version '{kernelVersion}'"
  let familyJson : List Json ← required json "families" context
  if familyJson.isEmpty then throw "observation bundle must contain at least one family"
  let families ← familyJson.mapM parseFamily
  if (firstDuplicate? familyIdentityOrder families).isSome then
    throw "observation bundle has duplicate family/projection/version identity"
  pure { schemaVersion, kernelVersion, families }

def Bundle.parseText (input : String) : Except String Bundle := do
  if input.utf8ByteSize > maxBytes then
    throw s!"observation bundle exceeds the {maxBytes}-byte limit"
  let json ← match A12Kernel.Reference.StrictJson.parseEvidence input with
    | .ok json => pure json
    | .error error => throw s!"observation bundle: invalid strict JSON: {repr error}"
  Bundle.fromJson json

def Bundle.load (path : System.FilePath) : IO Bundle := do
  let input ← A12Kernel.Process.ArtifactTree.readBoundedText
    path "semantic observation bundle" maxBytes
  match Bundle.parseText input with
  | .ok bundle => pure bundle
  | .error error => throw (IO.userError s!"{path}: {error}")

end A12Kernel.Evidence.ObservationBundle
