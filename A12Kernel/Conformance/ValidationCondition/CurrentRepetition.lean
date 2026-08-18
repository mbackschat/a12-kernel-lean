import A12Kernel.Elaboration.ValidationCondition

/-! # Exact nonrepeatable-root CurrentRepetition condition locks -/

namespace A12Kernel.Conformance.ValidationCondition.CurrentRepetition

open A12Kernel

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

end A12Kernel.Conformance.ValidationCondition.CurrentRepetition
