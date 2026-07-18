import A12Kernel.Evidence.ObservationBundle
import A12Kernel.Process.Sha256
import A12Kernel.Semantics.StringCascade

/-! # Compact direct String-cascade observation family

This nontrusted projection assigns the five producer-certified case payloads their narrow A12 meaning and compares them with the real two-step Lean evaluator. Observation lists use canonical semantic target order—producer `mid` before consumer `out`—and preserve multiplicity; incidental raw runner order remains only in the opaque packet. The projection deliberately excludes raw runner, packet, scheduling, and exact absent-versus-present-empty state.
-/

namespace A12Kernel.Evidence.StringCascadeProjection

open Lean
open A12Kernel
open A12Kernel.Evidence.ObservationBundle

def familyId := "string-direct-cascade-v1"
def projectionId := "string-direct-cascade-semantic-v1"
def projectionVersion : Nat := 1
def producerRevision := "1b5f463b89adc6cfb81b41121cd6c97855e8cbe3"
def bundleSha256 := "1d8d253e553eba70fa990975666884833748bed9d9b2b6483f472767a9837c7a"
private def bundleFile := "semantic-observations.json"
private def rawReceiptPath := "packet/RECEIPT.json"
private def rawReceiptDigest := "7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17"
private def qualificationReceiptPath := "qualification/RECEIPT.json"
private def qualificationReceiptDigest := "f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64"

inductive Target where
  | mid
  | out
  deriving Repr, DecidableEq

structure Input where
  source : Option String
  priorMid : PriorStringTarget
  priorOut : PriorStringTarget
  deriving Repr, DecidableEq

structure ValueObservation where
  target : Target
  value : StoredString
  deriving Repr, DecidableEq

structure ErrorObservation where
  target : Target
  attempted : StoredString
  cause : StringTargetError
  deriving Repr, DecidableEq

structure AppliedObservation where
  target : Target
  value : Option StoredString
  deriving Repr, DecidableEq

structure Observation where
  clean : List ValueObservation
  changed : List ValueObservation
  errors : List ErrorObservation
  cleared : List Target
  applied : List AppliedObservation
  deriving Repr, DecidableEq

structure Case where
  id : String
  input : Input
  observed : Observation
  deriving Repr, DecidableEq

private def Target.parse (context : String) : String → Except String Target
  | "mid" => pure .mid
  | "out" => pure .out
  | other => throw s!"{context}: unsupported target '{other}'"

private def StringTargetError.parse (context : String) : String → Except String StringTargetError
  | "tooShort" => pure .tooShort
  | "tooLong" => pure .tooLong
  | other => throw s!"{context}: unsupported target error '{other}'"

private def nullableString (json : Json) (context : String) : Except String (Option String) :=
  match json with
  | .null => pure none
  | json =>
      match json.getStr? with
      | .ok value => pure (some value)
      | .error _ => throw s!"{context}: expected a string or null"

private def storedString (value context : String) : Except String StoredString :=
  if nonempty : value ≠ "" then pure { text := value, nonempty }
  else throw s!"{context}: stored String must not be empty"

private def nullableStoredString (json : Json)
    (context : String) : Except String (Option StoredString) := do
  match ← nullableString json context with
  | none => pure none
  | some value => some <$> storedString value context

private def priorTarget (json : Json) (context : String) : Except String PriorStringTarget := do
  match ← nullableStoredString json context with
  | none => pure .empty
  | some value => pure (.filled value)

private def Input.fromJson (context : String) (json : Json) : Except String Input := do
  Decode.requireObject json ["source", "priorMid", "priorOut"] context
  pure {
    source := ← nullableString (← Decode.requiredJson json "source" context) s!"{context}.source"
    priorMid := ← priorTarget (← Decode.requiredJson json "priorMid" context) s!"{context}.priorMid"
    priorOut := ← priorTarget (← Decode.requiredJson json "priorOut" context) s!"{context}.priorOut" }

private def ValueObservation.fromJson (context : String)
    (json : Json) : Except String ValueObservation := do
  Decode.requireObject json ["target", "value"] context
  let value : String ← Decode.required json "value" context
  pure {
    target := ← Target.parse context (← Decode.required json "target" context)
    value := ← storedString value s!"{context}.value" }

private def ErrorObservation.fromJson (context : String)
    (json : Json) : Except String ErrorObservation := do
  Decode.requireObject json ["target", "attempted", "cause"] context
  let attempted : String ← Decode.required json "attempted" context
  pure {
    target := ← Target.parse context (← Decode.required json "target" context)
    attempted := ← storedString attempted s!"{context}.attempted"
    cause := ← StringTargetError.parse context (← Decode.required json "cause" context) }

private def AppliedObservation.fromJson (context : String)
    (json : Json) : Except String AppliedObservation := do
  Decode.requireObject json ["target", "value"] context
  pure {
    target := ← Target.parse context (← Decode.required json "target" context)
    value := ← nullableStoredString (← Decode.requiredJson json "value" context) s!"{context}.value" }

private def Observation.fromJson (caseId : String) (json : Json) : Except String Observation := do
  let context := s!"direct-cascade case '{caseId}' observed"
  Decode.requireObject json ["clean", "changed", "errors", "cleared", "applied"] context
  let cleanJson : List Json ← Decode.required json "clean" context
  let changedJson : List Json ← Decode.required json "changed" context
  let errorJson : List Json ← Decode.required json "errors" context
  let clearedText : List String ← Decode.required json "cleared" context
  let appliedJson : List Json ← Decode.required json "applied" context
  pure {
    clean := ← cleanJson.zipIdx.mapM fun (entry, index) =>
      ValueObservation.fromJson s!"{context}.clean[{index}]" entry
    changed := ← changedJson.zipIdx.mapM fun (entry, index) =>
      ValueObservation.fromJson s!"{context}.changed[{index}]" entry
    errors := ← errorJson.zipIdx.mapM fun (entry, index) =>
      ErrorObservation.fromJson s!"{context}.errors[{index}]" entry
    cleared := ← clearedText.zipIdx.mapM fun (target, index) =>
      Target.parse s!"{context}.cleared[{index}]" target
    applied := ← appliedJson.zipIdx.mapM fun (entry, index) =>
      AppliedObservation.fromJson s!"{context}.applied[{index}]" entry }

private def priorValue (value : String) (nonempty : value ≠ "") : PriorStringTarget :=
  .filled { text := value, nonempty }

private def stale := priorValue "STALE" (by decide)

private def expectedInputs : List (String × Input) := [
  ("source-abc-mid-old", { source := some "ABC", priorMid := priorValue "OLD" (by decide), priorOut := stale }),
  ("source-abc-mid-abc", { source := some "ABC", priorMid := priorValue "ABC" (by decide), priorOut := stale }),
  ("source-absent-mid-old", { source := none, priorMid := priorValue "OLD" (by decide), priorOut := stale }),
  ("source-absent-mid-absent", { source := none, priorMid := .empty, priorOut := stale }),
  ("source-abcd-mid-old", { source := some "ABCD", priorMid := priorValue "OLD" (by decide), priorOut := stale })]

def decodeFamily (family : ObservationBundle.Family) : Except String (List Case) := do
  if family.id != familyId || family.projectionId != projectionId ||
      family.projectionVersion != projectionVersion then
    throw "direct-cascade family compatibility identity differs"
  if family.source.producer != "a12-dmkits" then
    throw "direct-cascade family producer must be a12-dmkits"
  if family.source.revision != producerRevision then
    throw "direct-cascade family producer revision differs"
  if family.source.rawCapture.path.toString != rawReceiptPath ||
      family.source.rawCapture.sha256.toString != rawReceiptDigest then
    throw "direct-cascade family raw receipt identity differs"
  match family.source.qualification with
  | none => throw "direct-cascade family requires a qualification identity"
  | some qualification =>
      if qualification.policyId != "kernel-route-confirmed-v1" then
        throw "direct-cascade family requires kernel-route-confirmed-v1"
      if qualification.receipt.path.toString != qualificationReceiptPath ||
          qualification.receipt.sha256.toString != qualificationReceiptDigest then
        throw "direct-cascade family qualification receipt identity differs"
  if family.cases.map (·.id) != expectedInputs.map (·.1) then
    throw "direct-cascade family differs from the closed five-case order"
  family.cases.zip expectedInputs |>.mapM fun (raw, expected) => do
    let input ← Input.fromJson s!"direct-cascade case '{raw.id}' input" raw.input
    if input != expected.2 then
      throw s!"direct-cascade case '{raw.id}' differs from the closed input matrix"
    pure {
      id := raw.id
      input
      observed := ← Observation.fromJson raw.id raw.observed }

private def checkedString : Option String → CheckedCell
  | none => formalCheck { kind := .string } .empty
  | some value => formalCheck { kind := .string } (.parsed (.str value))

private def computationContext (input : Input) : StringComputationContext where
  read field :=
    if field == 1 then checkedString input.source
    else if field == 2 then
      match input.priorMid with
      | .empty => checkedString none
      | .filled value => checkedString (some value.text)
    else checkedString none

private def cascade (input : Input) : StringDirectCascade := {
    producer := {
      targetField := 2
      expression := .field 1
      targetPolicy := .maximum { value := 3, positive := by decide }
      prior := input.priorMid }
    consumer := {
      targetField := 3
      expression := .concat (.field 2) (.literal "-X")
      targetPolicy := .unconstrained
      prior := input.priorOut } }

private def clean (target : Target) : StringTargetOutcome → List ValueObservation
  | .accepted value => [{ target, value }]
  | _ => []

private def changed (target : Target) : Option StringDelta → List ValueObservation
  | some (.value value) => [{ target, value }]
  | _ => []

private def cleared (target : Target) : Option StringDelta → List Target
  | some .cleared => [target]
  | _ => []

private def errors (target : Target) : StringTargetOutcome → List ErrorObservation
  | .errored attempted cause => [{
      target
      attempted
      cause }]
  | _ => []

private def applied (target : Target) (outcome : StringTargetOutcome) : AppliedObservation := {
  target
  value := outcome.appliedValue }

private def project (result : StringDirectCascadeResult) : Observation := {
  clean := clean .mid result.producer.outcome ++ clean .out result.consumer.outcome
  changed := changed .mid result.producer.delta ++ changed .out result.consumer.delta
  errors := errors .mid result.producer.outcome ++ errors .out result.consumer.outcome
  cleared := cleared .mid result.producer.delta ++ cleared .out result.consumer.delta
  applied := [applied .mid result.producer.outcome, applied .out result.consumer.outcome] }

abbrev CascadeEvaluator :=
  StringDirectCascade → StringComputationContext →
    Except StringDirectCascadeFault StringDirectCascadeResult

def replayWith (evaluate : CascadeEvaluator) (input : Input) : Except String Observation := do
  let result ← match evaluate (cascade input) (computationContext input) with
    | .ok result => pure result
    | .error fault => throw s!"direct cascade left the admitted fragment: {repr fault}"
  pure (project result)

def replay : Input → Except String Observation :=
  replayWith StringDirectCascade.evaluate

def mismatchIds (replay : Input → Except String Observation)
    (family : ObservationBundle.Family) : Except String (List String) := do
  let cases ← decodeFamily family
  let mut mismatches := []
  for case in cases do
    let actual ← match replay case.input with
      | .ok observation => pure observation
      | .error error => throw s!"{case.id}: {error}"
    if actual != case.observed then mismatches := case.id :: mismatches
  pure mismatches.reverse

private def ioOrThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

def checkArtifacts (captureRoot : System.FilePath) : IO Nat := do
  let path := captureRoot / bundleFile
  let actualSha256 ← A12Kernel.Process.Sha256.file path
  if actualSha256 != bundleSha256 then
    throw (IO.userError
      s!"direct-cascade compact bundle digest differs: expected {bundleSha256}, found {actualSha256}")
  let bundle ← ObservationBundle.Bundle.load path
  let family ← match bundle.families with
    | [family] => pure family
    | _ => throw (IO.userError "direct-cascade compact bundle must contain exactly one family")
  let mismatches ← ioOrThrow "direct-cascade compact replay" (mismatchIds replay family)
  if !mismatches.isEmpty then
    throw (IO.userError s!"direct-cascade compact replay mismatched cases: {repr mismatches}")
  pure family.cases.length

end A12Kernel.Evidence.StringCascadeProjection
