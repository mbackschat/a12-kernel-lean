import A12Kernel.Evidence.ObservationBundle
import A12Kernel.Process.Sha256
import A12Kernel.Semantics.StringApplication

/-! # Compact root-String computation observations

This nontrusted lane gives two historical kernel captures one small typed meaning. The first record observes only root deltas; the second additionally observes the checked outcome and exact one-target application state. Both records use the sole closed target `/Shipment[1]/Target`. Raw models, placements, runner tables, and interpreter triangulation remain historical audit material rather than live replay inputs.

`rowHasContent` is deliberately retained while the unconditional evaluator ignores it: the paired empty-row cases empirically assert that no validation-style row gate belongs here.
-/

namespace A12Kernel.Evidence.StringComputationProjection

open Lean
open A12Kernel
open A12Kernel.Evidence.ObservationBundle

def bundleSha256 := "589ab2268c3347614b524a52a5667bfe5706e2a7a60f09d995da71068ea96d72"
private def bundleFile := "captures/string-computation-v1/semantic-observations.json"
private def familyId := "string-root-computation-v1"
private def sourceRevision := "23f35e3c23e53283defeb15e792901f9637238f5"

inductive Mode where
  | deltaOnly
  | targetChecked
  deriving Repr, DecidableEq

inductive Operation where
  | copy
  | suffix
  | appendFields
  | padded
  deriving Repr, DecidableEq

structure Input where
  operation : Operation
  source : Option String
  other : Option String
  prior : StringTargetState
  rowHasContent : Bool
  policy : StringTargetLengthPolicy
  deriving Repr, DecidableEq

structure Observation where
  outcome : Option StringTargetOutcome
  delta : Option StringDelta
  applied : Option StringTargetState
  deriving Repr, DecidableEq

structure Case where
  id : String
  mode : Mode
  input : Input
  observed : Observation
  deriving Repr, DecidableEq

private def storedString (value context : String) : Except String StoredString :=
  if nonempty : value ≠ "" then pure { text := value, nonempty }
  else throw s!"{context}: stored String must not be empty"

private def nullableString (json : Json) (context : String) : Except String (Option String) :=
  match json with
  | .null => pure none
  | json =>
      match json.getStr? with
      | .ok value => do
          let stored ← storedString value context
          pure (some stored.text)
      | .error _ => throw s!"{context}: expected a nonempty string or null"

private def Operation.parse (context : String) : String → Except String Operation
  | "copy" => pure .copy
  | "suffix" => pure .suffix
  | "appendFields" => pure .appendFields
  | "padded" => pure .padded
  | other => throw s!"{context}: unsupported operation '{other}'"

private def Operation.toCore : Operation → StringExpr
  | .copy => .field 1
  | .suffix => .concat (.field 1) (.literal "-X")
  | .appendFields => .concat (.field 1) (.field 2)
  | .padded => .concat (.concat (.literal " ") (.field 1)) (.literal " ")

private def parsePolicy (json : Json) (context : String) :
    Except String StringTargetLengthPolicy := do
  let tag : String ← Decode.required json "tag" context
  match tag with
  | "unconstrained" =>
      Decode.requireObject json ["tag"] context
      pure .unconstrained
  | "minimum" | "maximum" =>
      Decode.requireObject json ["tag", "bound"] context
      let bound : Nat ← Decode.required json "bound" context
      if positive : 0 < bound then
        let value : PositiveStringLength := { value := bound, positive }
        pure <| if tag == "minimum" then .minimum value else .maximum value
      else throw s!"{context}: length bound must be positive"
  | other => throw s!"{context}: unsupported policy '{other}'"

private def parsePrior (json : Json) (context : String) : Except String StringTargetState := do
  match ← nullableString json context with
  | none => pure .absent
  | some value => pure (.presentValue (← storedString value context))

private def parseCause (context : String) : String → Except String StringTargetError
  | "tooShort" => pure .tooShort
  | "tooLong" => pure .tooLong
  | other => throw s!"{context}: unsupported target error '{other}'"

private def parseDelta (json : Json) (context : String) : Except String (Option StringDelta) := do
  if json == .null then return none
  let tag : String ← Decode.required json "tag" context
  match tag with
  | "value" =>
      Decode.requireObject json ["tag", "value"] context
      pure <| some (.value (← storedString (← Decode.required json "value" context) context))
  | "cleared" =>
      Decode.requireObject json ["tag"] context
      pure (some .cleared)
  | "errored" =>
      Decode.requireObject json ["tag", "attempted", "cause"] context
      pure <| some (.errored
        (← storedString (← Decode.required json "attempted" context) context)
        (← parseCause context (← Decode.required json "cause" context)))
  | other => throw s!"{context}: unsupported delta '{other}'"

private def parseOutcome (json : Json) (context : String) : Except String StringTargetOutcome := do
  let tag : String ← Decode.required json "tag" context
  match tag with
  | "accepted" =>
      Decode.requireObject json ["tag", "value"] context
      pure (.accepted (← storedString (← Decode.required json "value" context) context))
  | "errored" =>
      Decode.requireObject json ["tag", "attempted", "cause"] context
      pure (.errored
        (← storedString (← Decode.required json "attempted" context) context)
        (← parseCause context (← Decode.required json "cause" context)))
  | other => throw s!"{context}: unsupported checked outcome '{other}'"

private def parseApplied (json : Json) (context : String) : Except String StringTargetState := do
  let tag : String ← Decode.required json "tag" context
  match tag with
  | "absent" =>
      Decode.requireObject json ["tag"] context
      pure .absent
  | "presentEmpty" =>
      Decode.requireObject json ["tag"] context
      pure .presentEmpty
  | "presentValue" =>
      Decode.requireObject json ["tag", "value"] context
      pure (.presentValue (← storedString (← Decode.required json "value" context) context))
  | other => throw s!"{context}: unsupported applied state '{other}'"

private def Input.fromJson (mode : Mode) (caseId : String) (json : Json) : Except String Input := do
  let context := s!"String computation case '{caseId}' input"
  Decode.requireObject json ["operation", "source", "other", "prior", "rowHasContent", "policy"] context
  let input : Input := {
    operation := ← Operation.parse context (← Decode.required json "operation" context)
    source := ← nullableString (← Decode.requiredJson json "source" context) s!"{context}.source"
    other := ← nullableString (← Decode.requiredJson json "other" context) s!"{context}.other"
    prior := ← parsePrior (← Decode.requiredJson json "prior" context) s!"{context}.prior"
    rowHasContent := ← Decode.required json "rowHasContent" context
    policy := ← parsePolicy (← Decode.requiredJson json "policy" context) s!"{context}.policy" }
  match mode, input.operation, input.policy, input.source, input.other with
  | .deltaOnly, .copy, .unconstrained, _, none
  | .deltaOnly, .suffix, .unconstrained, _, none
  | .deltaOnly, .appendFields, .unconstrained, _, _
  | .targetChecked, .copy, .minimum _, some _, none
  | .targetChecked, .copy, .maximum _, some _, none
  | .targetChecked, .padded, .minimum _, some _, none
  | .targetChecked, .padded, .maximum _, some _, none =>
      if mode == .targetChecked && !input.rowHasContent then
        throw s!"{context}: target-check cases require a content-bearing row"
      pure input
  | _, _, _, _, _ => throw s!"{context}: operation, policy, and cell shape leave the closed projection"

private def Observation.fromJson (mode : Mode) (caseId : String)
    (json : Json) : Except String Observation := do
  let context := s!"String computation case '{caseId}' observed"
  match mode with
  | .deltaOnly =>
      Decode.requireObject json ["delta"] context
      pure {
        outcome := none
        delta := ← parseDelta (← Decode.requiredJson json "delta" context) s!"{context}.delta"
        applied := none }
  | .targetChecked =>
      Decode.requireObject json ["outcome", "delta", "applied"] context
      pure {
        outcome := some (← parseOutcome (← Decode.requiredJson json "outcome" context) s!"{context}.outcome")
        delta := ← parseDelta (← Decode.requiredJson json "delta" context) s!"{context}.delta"
        applied := some (← parseApplied (← Decode.requiredJson json "applied" context) s!"{context}.applied") }

private def deltaCaseIds := [
  "direct-filled-target-stale-content", "direct-filled-target-equal",
  "direct-empty-target-stale-content", "direct-empty-target-absent-content",
  "direct-empty-target-absent-empty-row", "suffix-filled-target-stale-content",
  "suffix-empty-target-stale-content", "suffix-empty-target-absent-content",
  "suffix-empty-target-absent-empty-row", "all-empty-filled-target-stale-content",
  "all-empty-target-stale-content", "all-empty-target-absent-content",
  "all-empty-target-absent-empty-row"]

private def targetCaseIds := [
  "max4-stale-value", "max3-stale-errored", "max4-absent-value",
  "max3-absent-errored", "max4-equal-unchanged", "max3-equal-errored",
  "min5-boundary-value", "min5-short-errored", "spaced-boundary-value"]

private def decodeFamily (family : ObservationBundle.Family) (mode : Mode)
    (projection capturePath captureSha256 : String) (caseIds : List String) :
    Except String (List Case) := do
  if family.id != familyId || family.projectionId != projection ||
      family.projectionVersion != 1 then
    throw "String computation family compatibility identity differs"
  if family.source.producer != "a12-kernel-lean" ||
      family.source.revision != sourceRevision ||
      family.source.rawCapture.path != capturePath ||
      family.source.rawCapture.sha256 != captureSha256 ||
      family.source.qualification.isSome then
    throw "String computation family reviewed-source identity differs"
  if family.cases.map (·.id) != caseIds then
    throw "String computation family case inventory or order differs"
  family.cases.mapM fun raw => do
    pure {
      id := raw.id
      mode
      input := ← Input.fromJson mode raw.id raw.input
      observed := ← Observation.fromJson mode raw.id raw.observed }

def decodeBundle (bundle : ObservationBundle.Bundle) : Except String (List Case) :=
  match bundle.families with
  | [deltaFamily, targetFamily] => do
      let deltaCases ← decodeFamily deltaFamily .deltaOnly
        "string-unconstrained-delta-v1" "captures/string-computation-2026-07-15.json"
        "e6a31b7916fc99a8901b26d2a303e436a3909787904fb5803bafaa11d6b40b83"
        deltaCaseIds
      let targetCases ← decodeFamily targetFamily .targetChecked
        "string-target-validation-v1" "captures/string-target-validation-2026-07-15.json"
        "3281bac938fd4dbdb199050262bfb58c4b30eb9fde71cf30bd2858d0eef07b37"
        targetCaseIds
      pure (deltaCases ++ targetCases)
  | _ => throw "String computation bundle must contain its two ordered source families"

private def checkedString : Option String → CheckedCell
  | none => formalCheck { kind := .string } .empty
  | some value => formalCheck { kind := .string } (.parsed (.str value))

private def Input.context (input : Input) : StringComputationContext where
  read field := if field == 1 then checkedString input.source else checkedString input.other

structure Runner where
  evaluateRow : Bool → Bool
  store : StringTerm → StringStore
  check : StringTargetLengthPolicy → StringStore → StringTargetCheckResult
  project : StringTargetOutcome → PriorStringTarget → Option StringDelta
  apply : StringTargetOutcome → StringTargetState → StringTargetState

def naturalRunner : Runner where
  evaluateRow _ := true
  store := StringTerm.store
  check := StringTargetLengthPolicy.check
  project := StringTargetOutcome.projectDelta
  apply := StringTargetOutcome.applyTo

def replayWith (runner : Runner) (case : Case) : Except String Observation := do
  if !runner.evaluateRow case.input.rowHasContent then
    return {
      outcome := none
      delta := none
      applied := if case.mode == .targetChecked then some case.input.prior else none }
  let term ← match case.input.operation.toCore.eval case.input.context with
    | .ok term => pure term
    | .error fault => throw s!"{case.id}: String expression left the admitted fragment: {repr fault}"
  let outcome ← match runner.check case.input.policy (runner.store term) with
    | .supported outcome => pure outcome
    | .unsupported fault => throw s!"{case.id}: String target check left the admitted fragment: {repr fault}"
  pure {
    outcome := if case.mode == .targetChecked then some outcome else none
    delta := runner.project outcome case.input.prior.toDeltaPrior
    applied := if case.mode == .targetChecked then some (runner.apply outcome case.input.prior) else none }

def replay : Case → Except String Observation := replayWith naturalRunner

def mismatchIds (runner : Runner) (cases : List Case) : Except String (List String) := do
  let mut mismatches := []
  for case in cases do
    let actual ← replayWith runner case
    if actual != case.observed then mismatches := case.id :: mismatches
  pure mismatches.reverse

private def ioOrThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

def loadCases (root : System.FilePath) : IO (List Case) := do
  let path := root / bundleFile
  let actualSha256 ← A12Kernel.Process.Sha256.file path
  if actualSha256 != bundleSha256 then
    throw (IO.userError
      s!"String computation compact bundle digest differs: expected {bundleSha256}, found {actualSha256}")
  ioOrThrow "String computation compact bundle" <| decodeBundle (← ObservationBundle.Bundle.load path)

def checkArtifacts (root : System.FilePath) : IO Nat := do
  let cases ← loadCases root
  let mismatches ← ioOrThrow "String computation compact replay" (mismatchIds naturalRunner cases)
  if !mismatches.isEmpty then
    throw (IO.userError s!"String computation compact replay mismatched cases: {repr mismatches}")
  pure cases.length

end A12Kernel.Evidence.StringComputationProjection
