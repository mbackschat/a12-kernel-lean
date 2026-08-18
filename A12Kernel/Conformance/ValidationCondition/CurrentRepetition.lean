import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # Checked CurrentRepetition condition locks -/

namespace A12Kernel.Conformance.ValidationCondition.CurrentRepetition

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def customer : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "CustomerName"
  policy := { kind := .string }
}

private def otherOrderField : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "Other"
  policy := { kind := .string }
}

private def nestedField : FlatFieldDecl := {
  id := 3
  groupPath := ["Order", "Details"]
  name := "Detail"
  policy := { kind := .string }
}

private def otherRootField : FlatFieldDecl := {
  id := 4
  groupPath := ["Other"]
  name := "Value"
  policy := { kind := .string }
}

private def model : FlatModel := {
  fields := [customer, otherOrderField, nestedField, otherRootField]
}

private def fieldPath (groups : List String) (field : String) : SurfaceFieldPath := {
  base := .absolute
  groups
  field
}

private def groupPath (groups : List String) : SurfaceGroupPath := {
  base := .absolute
  groups
}

private def checked?
    (comparison : RootCurrentRepetitionComparison) :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGuardedRootCurrentRepetition
    model ["Order"] (fieldPath ["Order"] "CustomerName")
    (groupPath ["Order"]) comparison).toOption

private def raw (customerCell otherCell : RawCell) : RawFlatContext where
  read field :=
    if field == customer.id then customerCell
    else if field == otherOrderField.id then otherCell
    else .empty

private def context (customerCell otherCell : RawCell) :
    ValidationEvaluationContext := {
  fields := model.checkContext (raw customerCell otherCell)
  groups := GroupPresenceContext.unavailable
}

private def verdict?
    (comparison : RootCurrentRepetitionComparison)
    (customerCell otherCell : RawCell) :
    Option Verdict := do
  let checked ← checked? comparison
  pure (checked.core.evalFull (context customerCell otherCell) true)

private def retainedShape?
    (comparison : RootCurrentRepetitionComparison) :
    Option (FieldId × GroupPath × RootCurrentRepetitionComparison) := do
  let checked ← checked? comparison
  match checked.core with
  | .leaf (.guardedRootCurrentRepetition guard group retained) =>
      some (guard.id, group, retained)
  | _ => none

private def directCoreError?
    (rowGroup : GroupPath) (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison) :
    Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.checkCore model rowGroup
      (ValidationCondition.guardedRootCurrentRepetition guard group comparison)
      (by native_decide) with
  | .ok _ => none
  | .error error => some error

private def hasNoIterationScope
    (condition : ValidationCondition model) : Bool :=
  match condition.ordinaryIterationScope with
  | .ok none => true
  | _ => false

private def surfaceError? (rowGroup : GroupPath)
    (guard : SurfaceFieldPath) (group : SurfaceGroupPath) :
    Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.fromGuardedRootCurrentRepetition
      model rowGroup guard group .equalOne with
  | .ok _ => none
  | .error error => some error

/- Both measured operators retain the guard, ordinary root group, and closed comparison tag. -/
example :
    retainedShape? .equalOne = some (customer.id, ["Order"], .equalOne) ∧
      retainedShape? .notEqualOne =
        some (customer.id, ["Order"], .notEqualOne) := by
  native_decide

/- A filled direct guard exposes the nonrepeatable root's constant index one with VALUE polarity. -/
example :
    verdict? .equalOne (.parsed (.str "Acme")) .empty =
        some (.fired .value) ∧
      verdict? .notEqualOne (.parsed (.str "Acme")) .empty =
        some .notFired := by
  native_decide

/- Filling an unrelated field opens the full-validation content gate but cannot replace the direct guard. -/
example :
    verdict? .equalOne .empty (.parsed (.str "present")) =
      some .notFired := by
  native_decide

/- The existing guard semantics remain visible: formal invalidity is UNKNOWN. -/
example :
    verdict? .equalOne (.rejected .malformed) .empty = some .unknown := by
  native_decide

/- CurrentRepetition contributes no field dependency; the direct guard is the sole reference. -/
example :
    (checked? .equalOne).map (fun checked =>
      (checked.core.referencesField customer.id,
        checked.core.referencesField otherOrderField.id,
        (checked.core.referencePointers []).toOption)) =
      some (true, false,
        some [{ field := customer.id, coordinates := [] }]) := by
  native_decide

/- The exact root constant is scalar, reports `canFireOnEmpty = false`, and deliberately has no partial-validation interpretation. -/
example :
    (checked? .equalOne).map (fun checked =>
      (checked.core.canFireOnEmpty,
        checked.core.hasHaving,
        checked.core.requiresAddressedValidation,
        hasNoIterationScope checked.core,
        checked.core.supportsOrdinaryIteration,
        checked.core.allLeaves ValidationConditionLeaf.supportsAddressedPartial)) =
      some (false, false, false, true, true, false) := by
  native_decide

/- Public core checking rejects attempts to detach the guard from the same ordinary root or counterfeit its declaration. -/
example :
    directCoreError? ["Order"] otherRootField ["Order"] .equalOne =
        some .incoherentCore ∧
      directCoreError? ["Order"] otherRootField ["Other"] .equalOne =
        some .incoherentCore ∧
      directCoreError? ["Order", "Details"] nestedField
          ["Order", "Details"] .equalOne =
        some .incoherentCore ∧
      directCoreError? ["Order"] { customer with name := "Counterfeit" }
          ["Order"] .equalOne = some .incoherentCore := by
  native_decide

/- Surface assembly fails closed for cross-root, fixed-nested, and unknown groups. -/
example :
    surfaceError? ["Order"] (fieldPath ["Order"] "CustomerName")
        (groupPath ["Other"]) = some .incoherentCore ∧
      surfaceError? ["Order"] (fieldPath ["Other"] "Value")
        (groupPath ["Other"]) = some .incoherentCore ∧
      surfaceError? ["Order", "Details"]
        (fieldPath ["Order", "Details"] "Detail")
        (groupPath ["Order", "Details"]) = some .incoherentCore ∧
      surfaceError? ["Order"] (fieldPath ["Order"] "CustomerName")
        (groupPath ["Missing"]) = some (.unknownGroup ["Missing"]) := by
  native_decide

/-! ## Same-group repeatable row index -/

private def repeatableSections : RepeatableGroupDecl :=
  { level := 10, path := ["Order", "Sections"], repeatability := some 3 }

private def repeatableModel : FlatModel :=
  { ordinaryIterationModel with repeatableGroups := [
      repeatableSections,
      { level := 20, path := ["Order", "Sections", "Items"],
        repeatability := some 2 },
      { level := 30, path := ["Order", "Sections", "Notes"],
        repeatability := some 2 }] }

private def repeatableChecked?
    (comparison : RepeatableCurrentRepetitionComparison) :
    Option (CheckedValidationCondition repeatableModel) :=
  (CheckedValidationCondition.fromGuardedRepeatableCurrentRepetition
    repeatableModel ["Order"]
    (fieldPath ["Order", "Sections"] "OuterAmount")
    (groupPath ["Order", "Sections"]) comparison).toOption

private def repeatableRetainedShape?
    (comparison : RepeatableCurrentRepetitionComparison) :
    Option (FieldId × RepeatableLevel ×
      RepeatableCurrentRepetitionComparison) := do
  let checked ← repeatableChecked? comparison
  match checked.core with
  | .leaf (.guardedRepeatableCurrentRepetition guard group retained) =>
      some (guard.id, group.level, retained)
  | _ => none

private def repeatableRule?
    (comparison : RepeatableCurrentRepetitionComparison) :
    Option (CheckedResolvedValidationRule repeatableModel) := do
  let condition ← repeatableChecked? comparison
  (assembleResolvedValidationRule repeatableModel condition outerAmount.id
    "currentRepetition" .error { parts := [] }).toOption

private def repeatableData : DocumentData := {
  instantiatedRows := [
    { group := 10, path := [1] },
    { group := 10, path := [2] },
    { group := 10, path := [3] }]
  cells := [1, 2, 3].map fun row => {
    address := { field := outerAmount.id, path := [row] }
    stored := "5"
    raw := .parsed (.num 5) }
}

private def repeatableRuleSnapshot?
    (comparison : RepeatableCurrentRepetitionComparison) :
    Option (OrdinaryRuleIterationPlan ×
      List (Env × Verdict × Option MessagePointer)) := do
  let rule ← repeatableRule? comparison
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      repeatableModel).toOption
  let checked ← (checkDocument prepared "en_US" repeatableData).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull checked).toOption
  pure (rule.ordinaryIterationPlan, outcomes.map fun outcome =>
    (outcome.1, outcome.2.verdict,
      outcome.2.message?.map (·.errorAddress)))

private def repeatableAddressedResult?
    (environment : Env) (guardCell : RawCell := .parsed (.num 5)) :
    Option (Except CheckedAddressingError Verdict) := do
  let checked ← repeatableChecked? .greaterThanOne
  let fields := repeatableModel.checkContext { read := fun field =>
    if field == outerAmount.id then guardCell else RawCell.empty }
  let document : Document := { instantiatedRows := [], rawCells := fun _ => none }
  pure (checked.core.evalAddressed {
      scalar := { fields, groups := GroupPresenceContext.unavailable }
      outer := environment
      input := .legacy document (fun _ field => fields.read field) })

private def repeatableAddressedError?
    (environment : Env) : Option CheckedAddressingError := do
  let result ← repeatableAddressedResult? environment
  match result with
  | .ok _ => none
  | .error error => some error

private def repeatableAddressedVerdict?
    (environment : Env) (guardCell : RawCell := .parsed (.num 5)) :
    Option Verdict := do
  let result ← repeatableAddressedResult? environment guardCell
  result.toOption

private def repeatableSurfaceError?
    (guard : SurfaceFieldPath) (group : SurfaceGroupPath) :
    Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.fromGuardedRepeatableCurrentRepetition
      repeatableModel ["Order"] guard group .greaterThanOne with
  | .ok _ => none
  | .error error => some error

private def repeatableDirectError?
    (guard : FlatFieldDecl) (group : RepeatableGroupDecl) :
    Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.checkCore repeatableModel ["Order"]
      (ValidationCondition.guardedRepeatableCurrentRepetition
        guard group .greaterThanOne) (by native_decide) with
  | .ok _ => none
  | .error error => some error

private def repeatableIterationLegal? : Bool :=
  match repeatableChecked? .greaterThanOne with
  | some checked =>
      match checked.core.iterationLegality with
      | .ok .legal => true
      | _ => false
  | none => false

/- The checked leaf retains the direct guard, model-owned repeatable level, and one of the three measured comparison shapes. -/
example :
    repeatableRetainedShape? .greaterThanOne =
        some (outerAmount.id, 10, .greaterThanOne) ∧
      repeatableRetainedShape? .greaterThanTwo =
        some (outerAmount.id, 10, .greaterThanTwo) ∧
      repeatableRetainedShape? .greaterEqualOne =
        some (outerAmount.id, 10, .greaterEqualOne) := by
  native_decide

/- Full ordinary execution reads the selected row coordinate: `> 1` fires VALUE only beyond row one and attaches each firing to that row. -/
example :
    (repeatableRuleSnapshot? .greaterThanOne == some (
      .rows [10], [
        ([(10, 1)], .notFired, none),
        ([(10, 2)], .fired .value,
          some { field := outerAmount.id, coordinates := [.concrete 2] }),
        ([(10, 3)], .fired .value,
          some { field := outerAmount.id, coordinates := [.concrete 3] })])) = true := by
  native_decide

/- The internal total account separates row three from row two and the inclusive lower bound from `> 1`; external evidence for these exact coordinates remains pending. -/
example :
    (repeatableRuleSnapshot? .greaterThanTwo).map
        (·.2.map fun outcome => outcome.2.1) =
        some [.notFired, .notFired, .fired .value] ∧
      (repeatableRuleSnapshot? .greaterEqualOne).map
        (·.2.map fun outcome => outcome.2.1) =
        some [.fired .value, .fired .value, .fired .value] := by
  native_decide

/- Missing, duplicate, and zero bindings remain structural addressing errors rather than semantic UNKNOWN. -/
example :
    repeatableAddressedError? [] =
        some (.environment (.missingBinding 10)) ∧
      repeatableAddressedError? [(10, 1), (10, 2)] =
        some (.environment (.duplicateBinding 10)) ∧
      repeatableAddressedError? [(10, 0)] =
        some (.environment (.zeroBinding 10)) := by
  native_decide

/- The direct filled guard remains indivisible from the coordinate comparison: empty is false and malformed is UNKNOWN on the same firing row. -/
example :
    repeatableAddressedVerdict? [(10, 2)] = some (.fired .value) ∧
      repeatableAddressedVerdict? [(10, 2)] .empty = some .notFired ∧
      repeatableAddressedVerdict? [(10, 2)] (.rejected .malformed) =
        some .unknown := by
  native_decide

/- Surface and direct checked admission reject a detached group, a nonrepeatable group, and counterfeit retained declarations. -/
example :
    repeatableSurfaceError?
        (fieldPath ["Order", "Sections"] "OuterAmount")
        (groupPath ["Order", "Sections", "Items"]) =
      some .incoherentCore ∧
    repeatableSurfaceError?
        (fieldPath ["Order", "Sections"] "OuterAmount")
        (groupPath ["Order", "Sections", "Details"]) =
      some (.groupReference (.resolve
        (.unknownRepeatableGroup ["Order", "Sections", "Details"]))) ∧
    repeatableSurfaceError?
        (fieldPath ["Order", "Sections", "Details"] "SectionDetail")
        (groupPath ["Order", "Sections"]) =
      some .incoherentCore ∧
    repeatableDirectError? outerAmount
        { repeatableSections with repeatability := some 2 } =
      some .incoherentCore ∧
    repeatableDirectError? { outerAmount with name := "Counterfeit" }
        repeatableSections = some .incoherentCore := by
  native_decide

/- Analyze sees the filled guard as the only field dependency and pointer, while execution and partial-support queries expose the addressed boundary explicitly. -/
example :
    repeatableIterationLegal? = true ∧
    (((repeatableChecked? .greaterThanOne).map (fun checked =>
      (checked.core.canFireOnEmpty,
        checked.core.referencesField outerAmount.id,
        checked.core.hasHaving,
        checked.core.requiresAddressedValidation,
        checked.core.supportsOrdinaryIteration,
        checked.core.allLeaves ValidationConditionLeaf.supportsAddressedPartial,
        (checked.core.referencePointers [(10, 2)]).toOption)) ==
      some (false, true, false, true, true,
        false, some [{ field := outerAmount.id, coordinates := [.concrete 2] }])) = true) := by
  native_decide

end A12Kernel.Conformance.ValidationCondition.CurrentRepetition
