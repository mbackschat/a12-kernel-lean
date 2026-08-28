import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked direct-field computation formal-input inventory locks -/

namespace A12Kernel.Conformance.ComputationFormalInput

open A12Kernel

private def numberField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Order"], repeatableScope := []
  policy := { kind := .number { scale := 0, signed := true } }
  numericTargetConstraints := { maximum := some 0 }
}

private def operand := numberField 1 "Operand"
private def target := numberField 2 "Target"
private def finalTarget := numberField 3 "FinalTarget"
private def unrelated := numberField 4 "Unrelated"
private def model : FlatModel := {
  fields := [operand, target, finalTarget, unrelated]
}

private def rejected (field : FieldId) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored := "1"
  raw := .rejected .declaredConstraint
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [rejected operand.id, rejected target.id,
      rejected finalTarget.id, rejected unrelated.id]
  }).toOption

private def operations : List (FieldId × List FieldId) := [
  (target.id, [operand.id]),
  (finalTarget.id, [target.id, operand.id])
]

/- Authored duplicates normalize before collection, independently in the operand and computed-target sets. -/
example :
    (match checkComputationFormalInputPlan model
      [operand.id, operand.id] [target.id, target.id] with
    | .ok plan =>
        plan.operandFields == [operand.id] &&
          plan.computedFields == [target.id]
    | .error _ => false) = true := by
  native_decide

/- Unknown operand and computed-target identities retain their distinct plan roles. -/
example :
    (match checkComputationFormalInputPlan model [99] [] with
    | .error (.operandField field _) => field == 99
    | _ => false) = true := by
  native_decide

example :
    (match checkComputationFormalInputPlan model [] [99] with
    | .error (.computedField field _) => field == 99
    | _ => false) = true := by
  native_decide

/- Operation union keeps the direct source once and excludes both computed targets, including the intermediate read by its successor. -/
example :
    (do
      let plan ←
        checkComputationFormalInputOperations model operations |>.toOption
      let input ← input?
      pure (plan.operandFields.length, plan.computedFields.length,
        [plan.operandFields.contains operand.id,
          plan.operandFields.contains target.id,
          plan.computedFields.contains target.id,
          plan.computedFields.contains finalTarget.id],
        plan.findings input)) =
      some (2, 2, [true, true, true, true], [{
        address := { field := operand.id, path := [] }
        cause := .declaredConstraint
      }]) := by
  native_decide

/- Operation order does not change the extensional finding inventory. -/
example :
    (do
      let forward ←
        checkComputationFormalInputOperations model operations |>.toOption
      let reverse ←
        checkComputationFormalInputOperations model operations.reverse |>.toOption
      let input ← input?
      pure (forward.findings input, reverse.findings input)) = some ([{
        address := { field := operand.id, path := [] }
        cause := .declaredConstraint
      }], [{
        address := { field := operand.id, path := [] }
        cause := .declaredConstraint
      }]) := by
  native_decide

private def selectedIndex : FlatFieldDecl := {
  id := 10
  name := "SelectedIndex"
  groupPath := ["Order", "Selected"]
  repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def unusedIndex : FlatFieldDecl := {
  id := 11
  name := "UnusedIndex"
  groupPath := ["Order", "Unused"]
  repeatableScope := [20]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def defaultedIndex : FlatFieldDecl := {
  id := 12
  name := "DefaultedIndex"
  groupPath := ["Order", "Defaulted"]
  repeatableScope := [30]
  policy := { kind := .enumeration }
  enumeration := some {
    storedTokens := ["A", "B"]
    defaultStoredToken := some "B"
  }
}

private def computedIndex : FlatFieldDecl := {
  id := 13
  name := "ComputedIndex"
  groupPath := ["Order", "Computed"]
  repeatableScope := [40]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def unusedDefaultIndex : FlatFieldDecl := {
  defaultedIndex with
  id := 14
  name := "UnusedDefaultIndex"
  groupPath := ["Order", "UnusedDefault"]
  repeatableScope := [50]
}

private def selectedEmptyIndex : FlatFieldDecl := {
  id := 15
  name := "SelectedEmptyIndex"
  groupPath := ["Order", "SelectedEmpty"]
  repeatableScope := [60]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def generatedModel : FlatModel := {
  fields := [operand, target, selectedIndex, unusedIndex, defaultedIndex,
    computedIndex, unusedDefaultIndex, selectedEmptyIndex]
  repeatableGroups := [
    { level := 10, path := selectedIndex.groupPath,
      repeatability := some 2, indexField := some selectedIndex.id },
    { level := 20, path := unusedIndex.groupPath,
      repeatability := some 1, indexField := some unusedIndex.id },
    { level := 30, path := defaultedIndex.groupPath,
      repeatability := some 1, indexField := some defaultedIndex.id },
    { level := 40, path := computedIndex.groupPath,
      repeatability := some 1, indexField := some computedIndex.id },
    { level := 50, path := unusedDefaultIndex.groupPath,
      repeatability := some 1, indexField := some unusedDefaultIndex.id },
    { level := 60, path := selectedEmptyIndex.groupPath,
      repeatability := some 1, indexField := some selectedEmptyIndex.id }
  ]
}

private def generatedInput? : Option (CheckedDocument generatedModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler generatedModel).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1] }, { group := 30, path := [1] },
      { group := 40, path := [1] }, { group := 50, path := [1] },
      { group := 60, path := [1] }
    ]
    cells := [
      rejected operand.id,
      { address := { field := selectedIndex.id, path := [1] },
        stored := "5", raw := .parsed (.num 5) },
      { address := { field := selectedIndex.id, path := [2] },
        stored := "5", raw := .parsed (.num 5) }
    ]
  }).toOption

private def generatedFinding (field : FieldId) (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := { field, path }
  cause
}

/- Preparation retains eager cached findings, runs preliminary rules only for selected noncomputed index fields, and stages a selected declaration-owned default before that preliminary pass. -/
example :
    (do
      let input ← generatedInput?
      let plan ← (checkComputationFormalInputPlan generatedModel
        [operand.id, selectedIndex.id, defaultedIndex.id, computedIndex.id,
          selectedEmptyIndex.id]
        [target.id, computedIndex.id]).toOption
      let full ← input.applyFullIndexPreliminary.toOption
      let prepared ← (plan.prepare input).toOption
      let findings := prepared.formalErrorsInOperands
      pure (
        full.findingKindAt? { field := unusedIndex.id, path := [1] } ==
          some .mandatory &&
        full.findingKindAt? { field := computedIndex.id, path := [1] } ==
          some .mandatory &&
        prepared.preliminary.findingKindAt?
          { field := unusedIndex.id, path := [1] } == none &&
        prepared.preliminary.findingKindAt?
          { field := computedIndex.id, path := [1] } == none &&
        prepared.preliminary.defaultStoredAt?
          { field := defaultedIndex.id, path := [1] } == some "B" &&
        prepared.preliminary.defaultStoredAt?
          { field := unusedDefaultIndex.id, path := [1] } == some "B" &&
        prepared.preliminary.findingKindAt?
          { field := defaultedIndex.id, path := [1] } == none &&
        prepared.preliminary.findingKindAt?
          { field := selectedEmptyIndex.id, path := [1] } ==
            some .mandatory &&
        findings.length == 4 &&
        findings.contains
          (generatedFinding operand.id [] .declaredConstraint) &&
        findings.contains
          (generatedFinding selectedIndex.id [1] .duplicateIndex) &&
        findings.contains
          (generatedFinding selectedIndex.id [2] .duplicateIndex) &&
        findings.contains
          (generatedFinding selectedEmptyIndex.id [1] .required))) =
      some true := by
  native_decide

end A12Kernel.Conformance.ComputationFormalInput
