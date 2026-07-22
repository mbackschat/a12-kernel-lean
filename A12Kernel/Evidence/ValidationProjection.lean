import A12Kernel.Evidence.ObservationBundle
import A12Kernel.Process.Sha256
import A12Kernel.Reference.Evaluator
import A12Kernel.Semantics.Iteration
import A12Kernel.Semantics.Required

/-! # Compact retained validation observations

This nontrusted projection closes the remaining validation evidence without retaining a second model, path, or correlation interpreter. Current public cases stay attached to the normalized reference requests; only the absolute-required, operator-sensitive, and uncorrelated-iteration surfaces need small closed adapters. Suppression deliberately joins `notFired` and `unknown`, matching what the external authored-message observation can establish.
-/

namespace A12Kernel.Evidence.ValidationProjection

open Lean
open A12Kernel
open A12Kernel.Evidence

def bundleFile : System.FilePath :=
  "captures/validation-core-v1/semantic-observations.json"

def bundleSha256 :=
  "bd8f9411cd479b009a71e7c5a93e0369815c0a0b4647f6eacb5a4b1957532db7"

private def publicFamilyIds := [
  "flat-validation-empty-logic-v2",
  "flat-validation-directional-number-v2",
  "single-group-correlation-runtime-v2",
  "single-group-correlation-static-v2"]

private def privateFamilyIds := [
  "flat-path-required-private-v1",
  "operator-sensitive-empty-private-v1",
  "single-group-iteration-private-v1"]

private def expectedFamilyKeys : List (String × String × Nat) := [
  ("flat-validation-empty-logic-v2", "public-suite-evidence-association-v1", 1),
  ("flat-validation-directional-number-v2", "public-suite-evidence-association-v1", 1),
  ("single-group-correlation-runtime-v2", "public-suite-firing-rows-v1", 1),
  ("single-group-correlation-static-v2", "public-suite-static-outcome-v1", 1),
  ("flat-path-required-private-v1", "closed-scenario-focused-authored-v1", 1),
  ("operator-sensitive-empty-private-v1", "closed-model-rule-polarity-v1", 1),
  ("single-group-iteration-private-v1", "closed-sum-focused-authored-v1", 1)]

private def familyKey (family : ObservationBundle.Family) :=
  (family.id, family.projectionId, family.projectionVersion)

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else firstDuplicate? rest

def validateShape (bundle : ObservationBundle.Bundle) : Except String Unit := do
  if bundle.families.map familyKey != expectedFamilyKeys then
    throw "validation observation families differ from the closed identity and order"
  let publicFamilies := bundle.families.filter (publicFamilyIds.contains ·.id)
  let privateFamilies := bundle.families.filter (privateFamilyIds.contains ·.id)
  if let some duplicate := firstDuplicate?
      (publicFamilies.flatMap fun family => family.cases.map (·.id)) then
    throw s!"public validation observation duplicates case id '{duplicate}'"
  if let some duplicate := firstDuplicate?
      (privateFamilies.flatMap fun family => family.cases.map (·.id)) then
    throw s!"private validation observation duplicates case id '{duplicate}'"
  let publicCount := publicFamilies.foldl (fun total family => total + family.cases.length) 0
  let privateCount := privateFamilies.foldl (fun total family => total + family.cases.length) 0
  if publicCount != 25 || privateCount != 24 then
    throw s!"validation observation inventory is {publicCount} public and {privateCount} private cases"

def load (path : System.FilePath) : IO ObservationBundle.Bundle := do
  let actualSha256 ← A12Kernel.Process.Sha256.file path
  if actualSha256 != bundleSha256 then
    throw (IO.userError
      s!"validation observation bundle digest differs: expected {bundleSha256}, found {actualSha256}")
  let bundle ← ObservationBundle.Bundle.load path
  match validateShape bundle with
  | .ok () => pure bundle
  | .error error => throw (IO.userError error)

private def requireObject := ObservationBundle.Decode.requireObject
private def requiredJson := ObservationBundle.Decode.requiredJson
private def required [FromJson α] := ObservationBundle.Decode.required (α := α)

private def polarityTag : Polarity → String
  | .value => "value"
  | .omission => "omission"

def verdictObservation : Verdict → Json
  | .fired polarity =>
      Json.mkObj [("verdict", Json.mkObj [
        ("tag", toJson "fired"),
        ("polarity", toJson (polarityTag polarity))])]
  | .notFired | .unknown =>
      Json.mkObj [("suppressed", toJson true)]

private def requiredObservation : Verdict → Json
  | .fired polarity =>
      Json.mkObj [
        ("verdict", Json.mkObj [
          ("tag", toJson "fired"),
          ("polarity", toJson (polarityTag polarity))]),
        ("message", Json.mkObj [
          ("code", toJson "mandatoryField"),
          ("pointer", toJson "/Order[1]/Quantity")])]
  | verdict => verdictObservation verdict

private def rejectionObservation (kernelCode rejectionClass : String) : Json :=
  Json.mkObj [
    ("kernelCode", toJson kernelCode),
    ("rejectionClass", toJson rejectionClass)]

private def diagnosticObservation
    (code : A12Kernel.Reference.Support.DiagnosticCode) : Except String Json :=
  match code with
  | .shortNameNotUnique =>
      pure (rejectionObservation "MVK_FIELDNAME_NOT_UNIQUE" "shortNameNotUnique")
  | .unknownField =>
      pure (rejectionObservation "MVK_INVALID_ENTITY" "unknownField")
  | other => throw s!"private flat request produced unsupported diagnostic '{other.tag}'"

private def replayRequest (input : Json) : Except String Json := do
  let response ← match A12Kernel.Reference.evaluateText input.compress with
    | .ok response => pure response
    | .error failure => throw s!"reference evaluator failed internally: {repr failure}"
  match response with
  | .verdict verdict => pure (verdictObservation verdict)
  | .diagnostic diagnostic => diagnosticObservation diagnostic.code
  | .firingRows _ => throw "private flat request unexpectedly produced firing rows"

private def requiredRaw (input : Json) : Except String RawCell := do
  requireObject input ["state"] "absolute-required compact input"
  match (← required input "state" "absolute-required compact input" : String) with
  | "empty" => pure .empty
  | "filled" => pure (.parsed (.num 5))
  | "rejected" => pure (.rejected .malformed)
  | state => throw s!"unsupported absolute-required state '{state}'"

def replayRequired (input : Json) : Except String Json := do
  let policy : FieldPolicy := { kind := .number { scale := 2, signed := false } }
  let field : FlatField := .number { id := 0, info := { scale := 2, signed := false } }
  let raw ← requiredRaw input
  let context : FlatContext := {
    read := fun id => if id == 0 then formalCheck policy raw else formalCheck policy .empty }
  pure (requiredObservation (applyAbsoluteRequired field context).mandatoryVerdict)

private structure OperatorRule where
  code : String
  pointer : String
  condition : SurfaceCondition

private def absolute (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def stringModel : FlatModel := {
  fields := [{
    id := 0
    groupPath := ["Order"]
    name := "ProductCode"
    policy := { kind := .string } }]
  fieldRefByShortNameAllowed := false }

private def numberModel : FlatModel := {
  fields := [
    {
      id := 0
      groupPath := ["Order"]
      name := "StockOnHand"
      policy := { kind := .number { scale := 0, signed := false } }
    },
    {
      id := 1
      groupPath := ["Order"]
      name := "Quantity"
      policy := { kind := .number { scale := 0, signed := true } }
    }]
  fieldRefByShortNameAllowed := false }

private def stringRules : List OperatorRule := [
  {
    code := "STR_DIRECT"
    pointer := "/Order[1]/ProductCode"
    condition := .compare .equal (absolute "ProductCode") (.string "ABC")
  },
  {
    code := "STR_LEN_GE"
    pointer := "/Order[1]/ProductCode"
    condition := .lengthCompare .greaterEqual (absolute "ProductCode") 0
  },
  {
    code := "STR_LEN_LT"
    pointer := "/Order[1]/ProductCode"
    condition := .lengthCompare .less (absolute "ProductCode") 5
  }]

private def numberRules : List OperatorRule := [
  {
    code := "NUM_SIGNED_NE_NEG"
    pointer := "/Order[1]/Quantity"
    condition := .compare .notEqual (absolute "Quantity") (.number (-1))
  },
  {
    code := "NUM_UNSIGNED_NE_NEG"
    pointer := "/Order[1]/StockOnHand"
    condition := .compare .notEqual (absolute "StockOnHand") (.number (-1))
  },
  {
    code := "NUM_UNSIGNED_NE_POS"
    pointer := "/Order[1]/StockOnHand"
    condition := .compare .notEqual (absolute "StockOnHand") (.number 1)
  }]

private def replayWorld : World :=
  { now := { epochMillis := 0 } }

private def operatorMessage (rule : OperatorRule) (polarity : Polarity) : Json :=
  Json.mkObj [
    ("rule", toJson rule.code),
    ("polarity", toJson (polarityTag polarity)),
    ("pointer", toJson rule.pointer)]

private def replayRules (model : FlatModel) (raw : RawFlatContext)
    (hasContent : Bool) (rules : List OperatorRule) : Except String Json := do
  let mut messages := []
  for rule in rules do
    match elaborateAndEvalFull model replayWorld ["Order"] raw hasContent rule.condition with
    | .error error => throw s!"operator compact case left the admitted fragment: {repr error}"
    | .ok (.fired polarity) =>
        messages := messages ++ [operatorMessage rule polarity]
    | .ok .notFired | .ok .unknown => pure ()
  pure (Json.mkObj [("messages", toJson messages)])

def replayOperator (input : Json) : Except String Json := do
  requireObject input ["model", "value", "hasContent"] "operator compact input"
  let modelTag : String ← required input "model" "operator compact input"
  let value ← requiredJson input "value" "operator compact input"
  let hasContent : Bool ← required input "hasContent" "operator compact input"
  match modelTag, value with
  | "stringLength", .null =>
      replayRules stringModel { read := fun _ => .empty } hasContent stringRules
  | "stringLength", .str text =>
      replayRules stringModel { read := fun _ => .parsed (.str text) } hasContent stringRules
  | "directionalNumber", .null =>
      replayRules numberModel { read := fun _ => .empty } hasContent numberRules
  | "directionalNumber", value => do
      let number : Int ← match (fromJson? value : Except String Int) with
        | .ok number => pure number
        | .error _ => throw "directional Number value must be null or an integer"
      if number != 0 then throw "directional Number compact input admits only zero"
      replayRules numberModel { read := fun _ => .parsed (.num number) }
        hasContent numberRules
  | other, _ => throw s!"unsupported operator compact model '{other}'"

private inductive IterationCell where
  | empty
  | number (value : Rat)
  | rejected

private structure IterationRow where
  filter : IterationCell
  value : IterationCell

private def IterationCell.fromJson (json : Json) : Except String IterationCell :=
  match json with
  | .null => pure .empty
  | .str "rejected" => pure .rejected
  | value =>
      match (fromJson? value : Except String Int) with
      | .ok amount => pure (IterationCell.number amount)
      | .error _ => throw "iteration cell must be null, an integer, or 'rejected'"

private def IterationRow.fromJson (json : Json) : Except String IterationRow := do
  requireObject json ["filter", "value"] "iteration compact row"
  pure {
    filter := ← IterationCell.fromJson
      (← requiredJson json "filter" "iteration compact row")
    value := ← IterationCell.fromJson
      (← requiredJson json "value" "iteration compact row") }

private def checkedNumber (scale : Nat) : IterationCell → CheckedCell
  | .empty => formalCheck { kind := .number { scale, signed := false } } .empty
  | .number value =>
      formalCheck { kind := .number { scale, signed := false } } (.parsed (.num value))
  | .rejected =>
      formalCheck { kind := .number { scale, signed := false } } (.rejected .malformed)

private def authoredObservation : K → Json
  | .tru => Json.mkObj [("authored", Json.mkObj [("polarity", toJson "omission")])]
  | .fls | .unknown => Json.mkObj [("authored", Json.null)]

def replayIteration (input : Json) : Except String Json := do
  requireObject input ["filterEquals", "sumEquals", "rows"] "iteration compact input"
  let filterJson ← requiredJson input "filterEquals" "iteration compact input"
  let filterEquals ← match filterJson with
    | .null => pure none
    | value =>
        match fromJson? value with
        | .ok (number : Int) => pure (some (number : Rat))
        | .error _ => throw "iteration filterEquals must be null or an integer"
  let sumEquals : Int ← required input "sumEquals" "iteration compact input"
  let rowJson : List Json ← required input "rows" "iteration compact input"
  let rows ← rowJson.mapM IterationRow.fromJson
  if rows.length != 3 then throw "iteration compact input requires exactly three rows"
  let filterField : FlatNumberField := { id := 0, info := { scale := 2, signed := false } }
  let valueField : FlatNumberField := { id := 1, info := { scale := 0, signed := false } }
  let context : SingleGroupValidationContext := {
    group := 10
    candidates := [1, 2, 3]
    read := fun row fieldId =>
      match rows[row - 1]? with
      | none => checkedNumber 0 .empty
      | some values =>
          if fieldId == filterField.id then checkedNumber 2 values.filter
          else checkedNumber 0 values.value }
  let star : SingleStar := {
    valueField
    having := filterEquals.map fun expected =>
      .compare (.number (.ordinary .equal) filterField expected) }
  pure (authoredObservation (star.evalSumEquality context .equal sumEquals))

private def replayPrivateCase (family : ObservationBundle.Family)
    (case : ObservationBundle.ObservationCase) : Except String Json :=
  match family.id with
  | "flat-path-required-private-v1" =>
      if case.input.getObjVal? "state" |>.isOk then replayRequired case.input
      else replayRequest case.input
  | "operator-sensitive-empty-private-v1" => replayOperator case.input
  | "single-group-iteration-private-v1" => replayIteration case.input
  | other => throw s!"unsupported private validation family '{other}'"

def mismatchIds (bundle : ObservationBundle.Bundle) : Except String (List String) := do
  validateShape bundle
  let mut mismatches := []
  for family in bundle.families.filter (privateFamilyIds.contains ·.id) do
    for case in family.cases do
      let actual ← replayPrivateCase family case
      if actual != case.observed then mismatches := case.id :: mismatches
  pure mismatches.reverse

def selectPublicCase (bundle : ObservationBundle.Bundle)
    (caseId : String) : Except String ObservationBundle.ObservationCase := do
  validateShape bundle
  let found := bundle.families.filter (publicFamilyIds.contains ·.id)
    |>.flatMap (·.cases)
    |>.filter (·.id == caseId)
  match found with
  | [case] => pure case
  | [] => throw s!"public validation evidence case '{caseId}' is absent"
  | _ => throw s!"public validation evidence case '{caseId}' is duplicated"

def publicObservationView (observed : Json) : Except String Json := do
  let hasKernelCode := (observed.getObjVal? "kernelCode").isOk
  let hasRejectionClass := (observed.getObjVal? "rejectionClass").isOk
  if hasKernelCode != hasRejectionClass then
    throw "public rejection observation requires kernelCode and rejectionClass together"
  if hasKernelCode then
    requireObject observed ["kernelCode", "rejectionClass"] "public rejection observation"
    let kernelCode : String ← required observed "kernelCode" "public rejection observation"
    let rejectionClass : String ← required observed "rejectionClass" "public rejection observation"
    let expectedKernelCode ← match rejectionClass with
      | "missingInner" => pure "MVK_NO_ITERATION_FOR_WILDCARD"
      | "equalityScaleMismatch" => pure "MVK_INVALID_COMPARE_DEC_PLACES"
      | "fieldOutsideGroup" => pure "MVK_INVALID_ITERATION_IN_FILTER_CONDITION"
      | other => throw s!"unsupported public rejection class '{other}'"
    if kernelCode != expectedKernelCode then
      throw s!"public rejection class '{rejectionClass}' is paired with '{kernelCode}'"
    pure (Json.mkObj [("rejectionClass", toJson rejectionClass)])
  else
    pure observed

def checkArtifacts (root : System.FilePath) : IO Nat := do
  let bundle ← load (root / bundleFile)
  let mismatches ← match mismatchIds bundle with
    | .ok mismatches => pure mismatches
    | .error error => throw (IO.userError s!"compact validation replay: {error}")
  if !mismatches.isEmpty then
    throw (IO.userError s!"compact validation replay mismatched cases: {repr mismatches}")
  pure 24

end A12Kernel.Evidence.ValidationProjection
