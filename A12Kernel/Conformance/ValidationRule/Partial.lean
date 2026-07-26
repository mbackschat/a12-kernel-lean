import A12Kernel.Elaboration.ValidationRule

/-!
# Checked nonrepeatable partial-validation rule locks

This family remains independently buildable with `lake build A12Kernel.Conformance.ValidationRule.Partial`; the validation-rule conformance module is only its import umbrella.
-/

namespace A12Kernel.Conformance.ValidationRule.Partial

open A12Kernel

private def errorField (isGlobal : Bool) : FlatFieldDecl :=
  { id := 200
    groupPath := ["Order"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := true } }
    isGlobal }

private def otherField : FlatFieldDecl :=
  { id := 201
    groupPath := ["Order"]
    name := "Confirmed"
    policy := { kind := .boolean } }

private def model (isGlobal : Bool) : FlatModel :=
  { fields := [errorField isGlobal, otherField] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def errorFilled : SurfaceCondition :=
  .fieldFilled (path "Amount")

private def otherFilled : SurfaceCondition :=
  .fieldFilled (path "Confirmed")

private def bothFilled : SurfaceCondition :=
  .and errorFilled otherFilled

private def eitherFilled : SurfaceCondition :=
  .or errorFilled otherFilled

private def emptyAmountIsZero : SurfaceCondition :=
  .compare .equal (path "Amount") (.number 0)

private def world : World :=
  { now := { epochMillis := 0 } }

private def rawBothFilled : RawFlatContext where
  read id :=
    if id == (errorField false).id then .parsed (.num 1)
    else if id == otherField.id then .parsed (.bool true)
    else .empty

private def rawEmpty : RawFlatContext where
  read _ := .empty

private def checkedRule? (isGlobal : Bool) (condition : SurfaceCondition) :
    Option (CheckedResolvedValidationRule (model isGlobal)) := do
  let flat ← (elaborate (model isGlobal) ["Order"] condition).toOption
  let checked ← (CheckedValidationCondition.fromFlat flat).toOption
  (assembleResolvedValidationRule (model isGlobal) checked
    (errorField isGlobal).id "partial" .error { parts := [] }).toOption

private def partialVerdict? (isGlobal : Bool)
    (condition : SurfaceCondition) (raw : RawFlatContext)
    (scope : ValidationRelevanceScope) : Option (Option Verdict) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      (model isGlobal)).toOption
  let rule ← checkedRule? isGlobal condition
  match rule.evalPartial prepared "en_US" raw
      GroupPresenceContext.unavailable scope with
  | .error _ => none
  | .ok .skipped => some none
  | .ok (.evaluated outcome) => some (some outcome.verdict)

private def fullVerdict? (isGlobal : Bool)
    (condition : SurfaceCondition) (raw : RawFlatContext)
    (hasContent : Bool) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      (model isGlobal)).toOption
  let rule ← checkedRule? isGlobal condition
  let outcome ←
    (rule.evalFull prepared "en_US" raw GroupPresenceContext.unavailable
      hasContent).toOption
  pure outcome.verdict

private def onlyOther : ValidationRelevanceScope :=
  .partialSet [{
    path := otherField.path
    indices := [.all, .all]
  }]

private def nothing : ValidationRelevanceScope :=
  .partialSet []

/- A global error field is auto-relevant before the rule gate; the same non-global rule remains skipped. -/
example :
    partialVerdict? true bothFilled rawBothFilled onlyOther =
      some (some (.fired .value)) ∧
    partialVerdict? false bothFilled rawBothFilled onlyOther =
      some none := by
  native_decide

/- Once the global error field admits the rule, an omitted peer remains leaf UNKNOWN: `And` suppresses while the independently true `Or` still fires. -/
example :
    partialVerdict? true bothFilled rawBothFilled nothing =
      some (some .unknown) ∧
    partialVerdict? true eitherFilled rawBothFilled nothing =
      some (some (.fired .value)) := by
  native_decide

/- Partial relevance bypasses the full-validation content gate, so a relevant empty scalar instance can fire through Number-as-zero. Repeatable phantom-row construction is a separate SG2 boundary. -/
example :
    partialVerdict? true emptyAmountIsZero rawEmpty nothing =
      some (some (.fired .omission)) ∧
    fullVerdict? true emptyAmountIsZero rawEmpty false =
      some .notFired := by
  native_decide

end A12Kernel.Conformance.ValidationRule.Partial
