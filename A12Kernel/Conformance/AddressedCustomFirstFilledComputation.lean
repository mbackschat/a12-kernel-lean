import A12Kernel.Elaboration.AddressedCustomFirstFilledFormalInput

/-! # Exact-address repeatable Custom `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedCustomFirstFilledComputation

open A12Kernel

private def customType : CustomFieldTypeDeclaration := { name := "ReviewCode" }
private def otherType : CustomFieldTypeDeclaration := { name := "OtherCode" }
private def sameNameOtherPolicy : CustomFieldTypeDeclaration := {
  name := "ReviewCode"
  minLength := some 2
}

private def customField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (declared : Option CustomFieldTypeDeclaration := some customType) :
    FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .string }
  customType := declared
}

private def source := customField 1 "Code"
  ["Projects", "Choices"] [10, 20]

private def target := customField 2 "Selected"
  ["Projects", "Tasks"] [10, 30]

private def unrelated := customField 3 "Unrelated" ["Summary"] []
private def fixedTarget := customField 4 "Fixed" ["Summary"] []
private def ordinarySource := customField 5 "Ordinary"
  ["Projects", "Choices"] [10, 20] none
private def otherSource := customField 6 "OtherCode"
  ["Projects", "Choices"] [10, 20] (some otherType)
private def nestedSource := customField 7 "NestedCode"
  ["Projects", "Choices", "Details"] [10, 20, 40]
private def unboundTarget := customField 8 "UnboundSelected" ["OtherTasks"] [50]
private def policySource := customField 9 "PolicyCode"
  ["Projects", "Choices"] [10, 20] (some sameNameOtherPolicy)
private def rootSource := customField 10 "GlobalCode" ["GlobalChoices"] [60]

private def model : FlatModel := {
  fields := [source, target, unrelated, fixedTarget, ordinarySource,
    otherSource, nestedSource, unboundTarget, policySource, rootSource]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 3 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 2,
      indexField := some source.id },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 2 },
    { level := 40, path := ["Projects", "Choices", "Details"],
      repeatability := some 2 },
    { level := 50, path := ["OtherTasks"], repeatability := some 2 },
    { level := 60, path := ["GlobalChoices"], repeatability := some 2 }]
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def nestedSiblingStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [
    { name := "Choices", starred := true },
    { name := "Details", starred := true }]
  field := nestedSource.name
}

private def partialBindingStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [
    { name := "Choices" },
    { name := "Details", starred := true }]
  field := nestedSource.name
}

private def absoluteSiblingStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Projects" },
    { name := "Choices", starred := true }]
  field := source.name
}

private def selfStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Tasks", starred := true }]
  field := target.name
}

private def rootStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "GlobalChoices", starred := true }]
  field := rootSource.name
}

private def operation? :
    Option (CheckedAddressedCustomFirstFilledComputation model) :=
  (checkAddressedCustomFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked :
    Except AddressedCustomFirstFilledComputationElabError
      (CheckedAddressedCustomFirstFilledComputation model)) :
    Option AddressedCustomFirstFilledComputationElabError :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary separates target placement, Custom declaration identity, source shape and scope, and self-reference. -/
example :
    operation?.isSome = true ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] 99 (siblingStar source.name)) =
        some (.target (.unknownFieldId 99)) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Summary"] target.id (siblingStar source.name)) =
        some (.targetOutsideDeclaringGroup target.path ["Summary"]) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Choices"] ordinarySource.id
        (siblingStar source.name)) =
        some (.targetNotCustom ordinarySource.path) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar ordinarySource.name)) =
        some (.sourceCustomTypeMismatch ordinarySource.path customType none) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar otherSource.name)) =
        some (.sourceCustomTypeMismatch otherSource.path customType
          (some otherType)) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar policySource.name)) =
        some (.sourceCustomTypeMismatch policySource.path customType
          (some sameNameOtherPolicy)) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id nestedSiblingStar) =
        some (.sourceShape nestedSource.path) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id partialBindingStar) =
        some (.sourceScope nestedSource.path) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["OtherTasks"] unboundTarget.id absoluteSiblingStar) =
        some (.sourceScope source.path) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id rootStar) =
        some (.sourceScope rootSource.path) ∧
    elabError? (checkAddressedCustomFirstFilledComputation model
      ["Projects", "Tasks"] target.id selfStar) =
        some (.targetSelfReference target.id) := by
  native_decide

private def rejection : RegisteredCustomRejection := {
  projectCode := "REVIEW_CODE_INVALID"
}

private def validator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "BAD" then some rejection else none

private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == customType.name || name == otherType.name then
      some validator
    else
      none
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 10, path := [3] },
    { group := 20, path := [1, 1] },
    { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] },
    { group := 20, path := [3, 1] },
    { group := 30, path := [2, 2] }, { group := 30, path := [1, 1] },
    { group := 30, path := [3, 2] }, { group := 30, path := [2, 1] },
    { group := 30, path := [3, 1] }, { group := 30, path := [1, 2] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.str stored)
}

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def input? : Option (CheckedDocument model) :=
  document? [
    cell source.id [1, 1] "A7",
    cell source.id [2, 1] "BAD",
    cell target.id [1, 1] "A7",
    cell target.id [1, 2] "SEED",
    cell target.id [2, 1] "SEED",
    cell target.id [3, 1] "SEED",
    cell unrelated.id [] "SOURCE"]

/- Each physical target row scans only its enclosing parent's sibling Custom rows. A registered rejection remains the reached poison for its parent, while an empty extent remains no-value. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.result))) = some [
      (address target.id [2, 2], .poison (.registeredCustomValidation rejection)),
      (address target.id [1, 1], .value "A7"),
      (address target.id [3, 2], .noValue),
      (address target.id [2, 1], .poison (.registeredCustomValidation rejection)),
      (address target.id [3, 1], .noValue),
      (address target.id [1, 2], .value "A7")] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  row11 : StringTargetState
  row12 : StringTargetState
  row21 : StringTargetState
  row22 : StringTargetState
  row31 : StringTargetState
  row32 : StringTargetState
  unrelatedState : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "OLD",
    cell target.id [1, 2] "OLD",
    cell target.id [2, 1] "OLD",
    cell unrelated.id [] "KEEP"]
  let result ← operation.executeResult input
    ([.registeredCustomValidation rejection] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.string.cleared
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row22 := applied (address target.id [2, 2])
    row31 := applied (address target.id [3, 1])
    row32 := applied (address target.id [3, 2])
    unrelatedState := applied (address unrelated.id [])
  }

/- Exact source classification makes the first accepted token inert, applies only the changed sibling, and retains clears only for source-filled targets. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "A7"),
      (address target.id [1, 2], "A7")]
    changes := [(address target.id [1, 2], "A7")]
    cleared := [address target.id [2, 1], address target.id [3, 1]]
    row11 := .presentValue ⟨"OLD", by decide⟩
    row12 := .presentValue ⟨"A7", by decide⟩
    row21 := .presentEmpty
    row22 := .absent
    row31 := .presentEmpty
    row32 := .absent
    unrelatedState := .presentValue ⟨"KEEP", by decide⟩
  } := by
  native_decide

private def formalInput? : Option (CheckedDocument model) :=
  document? [
    cell source.id [1, 1] "A7",
    cell source.id [2, 1] "OK", cell source.id [2, 2] "OK",
    cell source.id [3, 1] "BAD",
    cell target.id [1, 1] "A7", cell target.id [1, 2] "SEED",
    cell target.id [2, 1] "SEED", cell target.id [3, 1] "SEED"]

private def preparedOutcomes? : Option (List (CellAddr × TokenComputationResult)) := do
  let operation ← operation?
  let input ← formalInput?
  let plan ← operation.formalInputPlan.toOption
  let prepared ← plan.prepare input |>.toOption
  let outcomes ← operation.executeWithRead input
    prepared.preliminary.readComputation |>.toOption
  pure (outcomes.map fun outcome => (outcome.targetField, outcome.result))

/- Custom preparation preserves the already-checked registered rejection, while generated duplicate poison remains a distinct prepared source outcome. -/
example : preparedOutcomes? = some [
    (address target.id [2, 2], .poison .duplicateIndex),
    (address target.id [1, 1], .value "A7"),
    (address target.id [3, 2], .poison (.registeredCustomValidation rejection)),
    (address target.id [2, 1], .poison .duplicateIndex),
    (address target.id [3, 1], .poison (.registeredCustomValidation rejection)),
    (address target.id [1, 2], .value "A7")] := by
  native_decide

private def formalFinding (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := address source.id path
  cause
}

private structure FormalInputSummary where
  planOperands : List FieldId
  planTargets : List FieldId
  findingsExact : Bool
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errorsEmpty : Bool
  cleared : List CellAddr
  deriving Repr, DecidableEq

private def formalInputSummary? : Option FormalInputSummary := do
  let operation ← operation?
  let input ← formalInput?
  let plan ← operation.formalInputPlan.toOption
  let result ← operation.executeResultWithFormalInputs input |>.toOption
  let findings := result.string.formalErrorsInOperands
  pure {
    planOperands := plan.operandFields
    planTargets := plan.computedFields
    findingsExact := findings.length == 3 &&
      findings.contains (formalFinding [3, 1]
        (.registeredCustomValidation rejection)) &&
      findings.contains (formalFinding [2, 1] .duplicateIndex) &&
      findings.contains (formalFinding [2, 2] .duplicateIndex)
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errorsEmpty := result.string.withErrors.isEmpty
    cleared := result.string.cleared
  }

/- The whole call retains both the pre-existing registered rejection and generated duplicates in its eager inventory, while both poison classes classify exact source-filled target clears. -/
example : formalInputSummary? = some {
    planOperands := [source.id]
    planTargets := [target.id]
    findingsExact := true
    values := [
      (address target.id [1, 1], "A7"),
      (address target.id [1, 2], "A7")]
    changes := [(address target.id [1, 2], "A7")]
    errorsEmpty := true
    cleared := [address target.id [2, 1], address target.id [3, 1]]
  } := by
  native_decide

end A12Kernel.Conformance.AddressedCustomFirstFilledComputation
