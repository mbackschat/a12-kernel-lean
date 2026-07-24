import A12Kernel.Elaboration.ValidationRule

/-!
# Checked repetition-not-unique whole-rule conformance locks

This family remains independently buildable with `lake build A12Kernel.Conformance.RepetitionNotUniqueValidationRule`; the conformance root is only its full-suite umbrella.
-/

namespace A12Kernel.Conformance.RepetitionNotUniqueValidationRule

open A12Kernel

private def count : FlatFieldDecl :=
  { id := 100
    groupPath := ["Order", "Items"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def weight : FlatFieldDecl :=
  { count with id := 101, name := "Weight" }

private def model : FlatModel :=
  { fields := [count, weight]
    repeatableGroups := [{
      level := 10
      path := ["Order", "Items"]
      repeatability := some 3 }] }

private def world : World :=
  { now := { epochMillis := 0 } }

private def field (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order", "Items"], field := name }

private def source (restKeys : List SurfaceFieldPath := []) :
    SurfaceRepetitionNotUniqueSource :=
  { firstKey := field "Count", restKeys }

private def checkedCondition? (restKeys : List SurfaceFieldPath := []) :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromRepetitionNotUnique
    model ["Order"] (source restKeys)).toOption

private def filledWeightCondition? :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    model ["Order"] .filled (field "Weight")).toOption

private def assembleRule?
    (combine : CheckedValidationCondition model →
      CheckedValidationCondition model →
        Except ValidationConditionAssemblyError
          (CheckedValidationCondition model))
    (restKeys : List SurfaceFieldPath := []) :
    Option (CheckedResolvedValidationRule model) := do
  let rnu ← checkedCondition? restKeys
  let filledWeight ← filledWeightCondition?
  let condition ← (combine rnu filledWeight).toOption
  (assembleResolvedValidationRule model condition count.id
    "rnu" .error { parts := [] }).toOption

private def rnuOrWeightRule? :
    Option (CheckedResolvedValidationRule model) :=
  assembleRule? CheckedValidationCondition.or

private def weightAndRnuRule? :
    Option (CheckedResolvedValidationRule model) :=
  assembleRule? (fun rnu filledWeight => filledWeight.and rnu)

private def compositeRnuRule? :
    Option (CheckedResolvedValidationRule model) := do
  let condition ← checkedCondition? [field "Weight"]
  (assembleResolvedValidationRule model condition count.id
    "rnu" .error { parts := [] }).toOption

private def cell (fieldId : FieldId) (row : Nat)
    (stored : String) (value : Nat) : ClassifiedCellInput :=
  { address := { field := fieldId, path := [row] }
    stored
    raw := .parsed (.num value) }

private def rnuOrWeightData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] }]
    cells := [
      cell count.id 1 "5" 5,
      cell count.id 2 "5" 5,
      cell count.id 3 "9" 9,
      cell weight.id 3 "200" 200] }

private def guardedRnuData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell count.id 1 "5" 5,
      cell count.id 2 "5" 5,
      cell weight.id 1 "1" 1] }

private def compositeRnuData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell count.id 1 "5" 5,
      cell count.id 2 "5" 5] }

private def checkedDocument? (data : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      model).toOption
  (checkDocument prepared "en_US" data).toOption

private def evalRule?
    (rule : CheckedResolvedValidationRule model)
    (data : DocumentData) :
    Option (List (Env × FlatRuleOutcome)) := do
  let document ← checkedDocument? data
  (rule.evalOrdinaryRepeatableFull document).toOption

private def verdicts?
    (rule : Option (CheckedResolvedValidationRule model))
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checked ← rule
  let outcomes ← evalRule? checked data
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

private def multipleRnuError? : Option ValidationConditionAssemblyError := do
  let first ← checkedCondition?
  let second ← checkedCondition?
  match first.and second with
  | .ok _ => none
  | .error error => some error

private def missingPreparedResultError? :
    Option CheckedAddressingError := do
  let condition ← checkedCondition?
  let document ← checkedDocument? rnuOrWeightData
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := [(10, 1)]
    input := .checked document
  }
  match condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def consumerKeyIds? : Option (List FieldId) := do
  let condition ← checkedCondition?
  let source ← condition.core.repetitionNotUniqueSource?
  pure (source.keys.map (·.fieldId))

private def consumerResults? :
    Option (List RepetitionNotUniqueResult) := do
  let condition ← checkedCondition?
  let source ← condition.core.repetitionNotUniqueSource?
  let document ← checkedDocument? guardedRnuData
  (source.evaluateChecked document [] .full).toOption

/- RNU remains one ordinary row leaf: duplicate rows fire through it, while an independent positive branch can fire the unique row. -/
example :
    verdicts? rnuOrWeightRule? rnuOrWeightData =
      some [
        ([(10, 1)], .fired .value),
        ([(10, 2)], .fired .value),
        ([(10, 3)], .fired .value)] := by
  native_decide

/- Duplicate construction is branch-independent: the guard-false peer still makes the guard-true row a duplicate. -/
example :
    verdicts? weightAndRnuRule? guardedRnuData =
      some [
        ([(10, 1)], .fired .value),
        ([(10, 2)], .notFired)] := by
  native_decide

/- Optional empty composite components participate in equality and retain OMISSION through whole-rule emission. -/
example :
    verdicts? compositeRnuRule? compositeRnuData =
      some [
        ([(10, 1)], .fired .omission),
        ([(10, 2)], .fired .omission)] := by
  native_decide

/- The checked condition rejects a second RNU leaf before runtime composition. -/
example :
    multipleRnuError? =
      some .multipleRepetitionNotUnique := by
  native_decide

/- Calling the generic addressed evaluator without the rule-owned RNU result is a structural execution failure, never semantic UNKNOWN. -/
example :
    missingPreparedResultError? =
      some (.repetitionNotUniqueResult [(10, 1)]) := by
  native_decide

/- Execute/Transform/Explain consumers recover the checked key identity and branch-independent peer cluster from the same source used by the row evaluator. -/
example :
    consumerKeyIds? = some [count.id] := by
  native_decide

example :
    consumerResults?.map (List.map fun result => result.verdict) =
      some [.fired .value, .fired .value] := by
  native_decide

example :
    consumerResults?.map (List.map fun result => result.cluster) =
      some [
        [[(10, 1)], [(10, 2)]],
        [[(10, 1)], [(10, 2)]]] := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueValidationRule
