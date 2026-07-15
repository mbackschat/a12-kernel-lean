import A12Kernel.Basic
import A12Kernel.Elaboration.Correlation
import A12Kernel.Evidence.AuthoringIdentifier
import A12Kernel.Evidence.CorrelationElaborationSchema

/-! # A12Kernel.Evidence.CorrelationElaborationReplay — pure authoring replay -/

namespace A12Kernel.Evidence.CorrelationElaboration

open A12Kernel

private def hasDuplicate [BEq α] (values : List α) : Bool :=
  match values with
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

/-- This evidence renderer deliberately supports only unquoted ASCII identifiers. Supporting the full quoted authoring grammar would require a separately tested canonical escaping layer. -/
private def safeSegment (segment : String) : Bool :=
  A12Kernel.Evidence.AuthoringIdentifier.safe segment

private def safePath (path : GroupPath) : Bool :=
  GroupPath.isValid path && path.all safeSegment

private def asciiLowerHex (character : Char) : Bool :=
  decide (character.toNat >= '0'.toNat && character.toNat <= '9'.toNat) ||
    decide (character.toNat >= 'a'.toNat && character.toNat <= 'f'.toNat)

example : safeSegment "Date" = false := by native_decide
example : safeSegment "Today" = false := by native_decide
example : safeSegment "Length" = false := by native_decide
example : safeSegment "Sum" = false := by native_decide
example : safeSegment "Valid" = false := by native_decide
example : safeSegment "and" = false := by native_decide
example : safeSegment "AND" = false := by native_decide

private def findGroupByLevel (groups : List RepeatableGroupSpec) (level : Nat) :
    Option RepeatableGroupSpec :=
  match groups with
  | [] => none
  | group :: rest => if group.level == level then some group else findGroupByLevel rest level

private def RepeatableGroupSpec.toDeclaration (group : RepeatableGroupSpec) :
    RepeatableGroupDecl :=
  { level := group.level, path := group.path }

private def NumberFieldSpec.toDeclaration (groups : List RepeatableGroupSpec)
    (field : NumberFieldSpec) : Except String FlatFieldDecl := do
  let group ← match findGroupByLevel groups field.groupLevel with
    | some group => pure group
    | none => throw s!"field {field.id} references unknown group level {field.groupLevel}"
  pure {
    id := field.id
    groupPath := group.path
    name := field.name
    policy := { kind := .number { scale := field.scale, signed := field.signed } }
    repeatableScope := [group.level] }

private def CaseSpec.model (case : CaseSpec) : Except String FlatModel := do
  pure {
    fields := ← case.fields.mapM (·.toDeclaration case.groups)
    repeatableGroups := case.groups.map (·.toDeclaration) }

private def RelativeFieldPathSpec.toSurface (path : RelativeFieldPathSpec) :
    SurfaceFieldPath :=
  { base := .relative 0, groups := path.groups, field := path.field }

private def RelativeStarFieldPathSpec.toSurface (path : RelativeStarFieldPathSpec) :
    SurfaceSingleStarFieldPath :=
  { base := .relative 0, groupsBeforeStar := path.groupsBeforeStar,
    starredGroup := path.starredGroup, field := path.field }

private def OriginSpec.toCore : OriginSpec → HavingOrigin
  | .inner => .inner
  | .outer => .outer

private def ComparisonOpSpec.toSurface : ComparisonOpSpec → SurfaceComparisonOp
  | .equal => .equal
  | .lessThan => .less

private def NumberRefSpec.toSurface (reference : NumberRefSpec) :
    SurfaceHavingNumberRef :=
  { origin := reference.origin.toCore, field := reference.field.toSurface }

private def HavingSpec.toSurface (having : HavingSpec) : SurfaceCorrelatedHaving :=
  .compareNumbers having.comparison.toSurface having.left.toSurface having.right.toSurface

private def RuleSpec.toSurface (rule : RuleSpec) : SurfaceSingleCorrelatedRule :=
  { errorField := rule.errorField.toSurface
    guardField := rule.guardField.toSurface
    valueField := rule.valueField.toSurface
    having := rule.having.toSurface }

private def RelativeFieldPathSpec.render (path : RelativeFieldPathSpec) : String :=
  String.intercalate "/" (path.groups ++ [path.field])

private def RelativeStarFieldPathSpec.render (path : RelativeStarFieldPathSpec) : String :=
  let group := String.intercalate "/" (path.groupsBeforeStar ++ [path.starredGroup])
  s!"{group}*/{path.field}"

private def OriginSpec.prefix : OriginSpec → String
  | .inner => ""
  | .outer => "$"

private def ComparisonOpSpec.token : ComparisonOpSpec → String
  | .equal => "=="
  | .lessThan => "<"

private def NumberRefSpec.render (reference : NumberRefSpec) : String :=
  s!"[{reference.origin.prefix}{reference.field.render}]"

private def HavingSpec.render (having : HavingSpec) : String :=
  s!"{having.left.render} {having.comparison.token} {having.right.render}"

structure DraftSignature where
  group : String
  name : String
  errorField : String
  condition : String
  errorCode : String
  severity : String
  deriving Repr, DecidableEq

def CaseSpec.renderDraft (case : CaseSpec) : DraftSignature :=
  let rule := case.rule
  {
    group := "/" ++ String.intercalate "/" rule.declaringGroup
    name := "LeanCorrelationElaborationProbe"
    errorField := "../" ++ rule.errorField.render
    condition := s!"FieldFilled({rule.guardField.render}) And AtLeastOneFieldFilled({rule.valueField.render} Having {rule.having.render})"
    errorCode := "LEAN_CORRELATION_ELABORATION"
    severity := "ERROR" }

def CaseSpec.renderSeedCondition (case : CaseSpec) : String :=
  s!"FieldFilled({case.rule.guardField.render})"

private def CaseSpec.validateTransport (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty then throw "correlation-elaboration evidence case id must not be empty"
  if case.caseRef.isEmpty then throw s!"{case.id}: caseRef must not be empty"
  if case.modelSha256.length != 64 || !case.modelSha256.toList.all asciiLowerHex then
    throw s!"{case.id}: modelSha256 must be a lowercase SHA-256 digest"
  if case.groups.isEmpty then throw s!"{case.id}: groups must not be empty"
  if case.fields.isEmpty then throw s!"{case.id}: fields must not be empty"
  if hasDuplicate (case.groups.map (·.level)) then throw s!"{case.id}: duplicate group level"
  if hasDuplicate (case.groups.map (·.path)) then throw s!"{case.id}: duplicate group path"
  for group in case.groups do
    if !safePath group.path then throw s!"{case.id}: invalid group path {repr group.path}"
  if hasDuplicate (case.fields.map (·.id)) then throw s!"{case.id}: duplicate field id"
  for field in case.fields do
    if !safeSegment field.name then throw s!"{case.id}: field {field.id} has an unsafe name"
    if !(case.groups.any (·.level == field.groupLevel)) then
      throw s!"{case.id}: field {field.id} references unknown group level {field.groupLevel}"
  if !safePath case.rule.declaringGroup then throw s!"{case.id}: invalid declaring group"
  let relativeFields := [case.rule.errorField, case.rule.guardField,
    case.rule.having.left.field, case.rule.having.right.field]
  for path in relativeFields do
    if path.groups.isEmpty || !path.groups.all safeSegment || !safeSegment path.field then
      throw s!"{case.id}: field references must be group-qualified and nonempty"
  let star := case.rule.valueField
  if !star.groupsBeforeStar.all safeSegment || !safeSegment star.starredGroup ||
      !safeSegment star.field then
    throw s!"{case.id}: invalid starred field path"
  let expectedRuleGroups := star.groupsBeforeStar ++ [star.starredGroup]
  if case.rule.errorField != case.rule.guardField then
    throw s!"{case.id}: error and guard fields must coincide in this projection"
  if case.rule.errorField.groups != expectedRuleGroups then
    throw s!"{case.id}: error and guard fields must be direct children of the starred group"
  let model ← case.model
  match model.validate with
  | .ok () => pure ()
  | .error error => throw s!"{case.id}: projected model is invalid: {repr error}"

/-- Only evidence-backed authoring outcomes may cross this projection. Every unclassified error fails closed. -/
private def diagnosticCode? : CorrelationElabError → Option String
  | .missingInner => some "MVK_NO_ITERATION_FOR_WILDCARD"
  | .equalityScaleMismatch _ _ _ _ => some "MVK_INVALID_COMPARE_DEC_PLACES"
  | .fieldOutsideGroup .inner _ _ => some "MVK_INVALID_ITERATION_IN_FILTER_CONDITION"
  | _ => none

example : diagnosticCode? .missingInner = some "MVK_NO_ITERATION_FOR_WILDCARD" := rfl
example : diagnosticCode? (.equalityScaleMismatch [] 0 [] 2) =
    some "MVK_INVALID_COMPARE_DEC_PLACES" := rfl
example : diagnosticCode? (.fieldOutsideGroup .inner [] []) =
    some "MVK_INVALID_ITERATION_IN_FILTER_CONDITION" := rfl
example : diagnosticCode? (.fieldOutsideGroup .outer [] []) = none := by native_decide
example : diagnosticCode? .missingOuter = none := rfl

def CaseSpec.replayDiagnosticCodes (case : CaseSpec) : Except String (List String) := do
  case.validateTransport
  let model ← case.model
  match elaborateSingleCorrelatedRule model case.rule.declaringGroup case.rule.toSurface with
  | .ok _ => pure []
  | .error error =>
      match diagnosticCode? error with
      | some code => pure [code]
      | none => throw s!"{case.id}: unsupported correlation-elaboration result: {repr error}"

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported correlation-elaboration evidence schema version {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"correlation-elaboration evidence targets kernel {bundle.kernelVersion}, Lean targets {A12Kernel.kernelVersion}"
  if bundle.cases.isEmpty then throw "correlation-elaboration evidence bundle is empty"
  if hasDuplicate (bundle.cases.map (·.id)) then
    throw "correlation-elaboration evidence case ids must be unique"
  for case in bundle.cases do
    case.validateTransport

private def transportFixture : CaseSpec := {
  id := "transport-guard"
  caseRef := "diagnostics/transport-guard.json"
  modelSha256 := "0000000000000000000000000000000000000000000000000000000000000000"
  groups := [{ level := 10, path := ["Order", "Items"] }]
  fields := [
    { id := 0, groupLevel := 10, name := "Count", scale := 0, signed := true },
    { id := 1, groupLevel := 10, name := "StockQty", scale := 0, signed := false },
    { id := 2, groupLevel := 10, name := "UnitWeight", scale := 2, signed := true }]
  rule := {
    declaringGroup := ["Order"]
    errorField := { groups := ["Items"], field := "Count" }
    guardField := { groups := ["Items"], field := "Count" }
    valueField := { groupsBeforeStar := [], starredGroup := "Items", field := "UnitWeight" }
    having := {
      comparison := .equal
      left := { origin := .inner, field := { groups := ["Items"], field := "StockQty" } }
      right := { origin := .outer, field := { groups := ["Items"], field := "StockQty" } } } } }

private def bundleFor (case : CaseSpec) : Bundle :=
  { schemaVersion := 1, kernelVersion := A12Kernel.kernelVersion, cases := [case] }

private def unsafeRenderedPathCase : CaseSpec :=
  let unsafePath : RelativeFieldPathSpec := { groups := ["Items] Or True"], field := "Count" }
  { transportFixture with rule := { transportFixture.rule with
      errorField := unsafePath, guardField := unsafePath } }

private def keywordRenderedPathCase : CaseSpec :=
  let keywordPath : RelativeFieldPathSpec := { groups := ["Items"], field := "Length" }
  { transportFixture with rule := { transportFixture.rule with
      errorField := keywordPath, guardField := keywordPath } }

private def wrongGuardRouteCase : CaseSpec :=
  { transportFixture with rule := { transportFixture.rule with
      errorField := { groups := ["Other"], field := "Count" }
      guardField := { groups := ["Other"], field := "Count" } } }

private def missingOuterCase : CaseSpec :=
  let innerRight := { transportFixture.rule.having.right with origin := .inner }
  { transportFixture with rule := { transportFixture.rule with
      having := { transportFixture.rule.having with right := innerRight } } }

example : (bundleFor unsafeRenderedPathCase).validate.isOk = false := by native_decide
example : (bundleFor keywordRenderedPathCase).validate.isOk = false := by native_decide
example : (bundleFor wrongGuardRouteCase).validate.isOk = false := by native_decide
example : missingOuterCase.replayDiagnosticCodes.isOk = false := by native_decide

end A12Kernel.Evidence.CorrelationElaboration
