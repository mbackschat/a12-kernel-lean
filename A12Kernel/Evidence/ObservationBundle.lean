import A12Kernel.Basic
import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! # Compact semantic-observation bundles

This nontrusted reader owns only the operation-neutral contract between a certified evidence producer and typed Lean family projections. Raw capture verification remains a producer responsibility. The `revision` is the producer implementation revision that certified the compact bundle; raw and qualification receipt identities separately anchor the historical capture. Their portable paths identify members of the recoverable producer unit and need not exist in the current checkout. The `qualification` member is always present on the wire; JSON `null` is its sole absent encoding.
-/

namespace A12Kernel.Evidence.ObservationBundle

open Lean

/-- Deliberate compact-export ceiling shared with the producer contract. -/
def maxBytes : Nat := 256 * 1024

private def isLowerHex (character : Char) : Bool :=
  decide ('0' ≤ character && character ≤ '9') ||
    decide ('a' ≤ character && character ≤ 'f')

/-- A closed portable identity for one receipt in a producer-owned recoverable unit. The compact reader does not re-audit that raw unit. -/
structure FileDigest where
  private mk ::
  path : String
  sha256 : String
  deriving Repr, BEq

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

namespace Decode

def requiredJson (json : Json) (name context : String) : Except String Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error _ => throw s!"{context}: missing member '{name}'"

def required [FromJson α] (json : Json) (name context : String) : Except String α := do
  let value ← requiredJson json name context
  match fromJson? value with
  | .ok decoded => pure decoded
  | .error _ => throw s!"{context}: member '{name}' has the wrong type"

def requireObject (json : Json) (allowed : List String)
    (context : String) : Except String Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => throw s!"{context}: expected an object"
  for (name, _) in object.toList do
    if !allowed.contains name then
      throw s!"{context}: unknown member '{name}'"

end Decode

open Decode

private def nonempty (value context : String) : Except String String := do
  if value.isEmpty then throw s!"{context}: must not be empty"
  pure value

private def gitRevision (value context : String) : Except String String := do
  if value.length != 40 || !value.toList.all isLowerHex then
    throw s!"{context}: expected a 40-character lowercase hexadecimal Git revision"
  pure value

private def isControl (character : Char) : Bool :=
  let code := character.toNat
  decide (code < 0x20) || decide (0x7f ≤ code && code ≤ 0x9f)

private def portableSegment (segment : String) : Except String Unit := do
  if segment.isEmpty then throw "portable path must not contain an empty segment"
  if segment.utf8ByteSize > 255 then
    throw "portable path segment exceeds 255 UTF-8 bytes"
  if segment == "." || segment == ".." then
    throw s!"portable path contains forbidden segment '{segment}'"
  if segment.startsWith "-" then
    throw s!"portable path segment must not start with '-': '{segment}'"
  if !segment.toList.all fun character =>
      decide (character.toNat < 0x80) &&
        (character.isAlphanum || ['.', '_', '-'].contains character) then
    throw s!"portable path segment contains a non-portable character: '{segment}'"

private def portablePath (value : String) : Except String String := do
  if value.isEmpty then throw "portable path must not be empty"
  if value.utf8ByteSize > 1024 then throw "portable path exceeds 1024 UTF-8 bytes"
  if value.startsWith "/" then throw "portable path must be relative"
  if value.contains '\\' then
    throw "portable path must use '/' separators, not backslashes"
  if value.contains ':' then throw "portable path must not contain ':'"
  if value.toList.any isControl then throw "portable path must not contain control characters"
  let segments := value.splitOn "/"
  if segments.length > 64 then throw "portable path exceeds 64 segments"
  for segment in segments do portableSegment segment
  pure value

private def sha256 (value : String) : Except String String := do
  if value.length != 64 then
    throw "SHA-256 digest must contain exactly 64 characters"
  if !value.toList.all isLowerHex then
    throw "SHA-256 digest must contain only lowercase hexadecimal characters"
  pure value

private def parseFileDigest (json : Json) (context : String) : Except String FileDigest := do
  requireObject json ["path", "sha256"] context
  let pathText : String ← required json "path" context
  let digestText : String ← required json "sha256" context
  let path ← match portablePath pathText with
    | .ok path => pure path
    | .error error => throw s!"{context}: member 'path': {error}"
  let digest ← match sha256 digestText with
    | .ok digest => pure digest
    | .error error => throw s!"{context}: member 'sha256': {error}"
  pure ⟨path, digest⟩

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
    receipt := ← parseFileDigest (← requiredJson json "receipt" context)
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
    rawCapture := ← parseFileDigest (← requiredJson json "rawCapture" context)
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

private def readBoundedText (path : System.FilePath) : IO String := do
  let metadata ← path.symlinkMetadata
  if metadata.type != .file then
    throw (IO.userError s!"semantic observation bundle '{path}' is not a regular non-symlink file")
  if metadata.byteSize > UInt64.ofNat maxBytes then
    throw (IO.userError s!"semantic observation bundle exceeds the {maxBytes}-byte limit")
  IO.FS.readFile path

def Bundle.load (path : System.FilePath) : IO Bundle := do
  let input ← readBoundedText path
  match Bundle.parseText input with
  | .ok bundle => pure bundle
  | .error error => throw (IO.userError s!"{path}: {error}")

end A12Kernel.Evidence.ObservationBundle
