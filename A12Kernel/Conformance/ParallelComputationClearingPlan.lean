import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Checked parallel-computation clearing-plan locks -/

namespace A12Kernel.Conformance.ParallelComputationClearingPlan

open A12Kernel

private def indexDeclaration (id : FieldId) (path : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name := "Key"
  policy := { kind := .string }
  repeatableScope := scope
}

private def numberDeclaration (id : FieldId) (path : GroupPath)
    (name : String) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := scope
}

private def frame : RepeatableGroupDecl := {
  level := 50
  path := ["Plan", "Frame"]
  repeatability := some 2
}

private def targetGroup : RepeatableGroupDecl := {
  level := 60
  path := ["Plan", "Frame", "Target"]
  repeatability := some 2
  indexField := some 1
}

private def operandGroup : RepeatableGroupDecl := {
  level := 70
  path := ["Plan", "Operand"]
  repeatability := some 2
  indexField := some 3
}

private def model : FlatModel := {
  fields := [
    indexDeclaration 1 targetGroup.path [50, 60],
    numberDeclaration 2 targetGroup.path "Result" [50, 60],
    numberDeclaration 5 targetGroup.path "Peer" [50, 60],
    indexDeclaration 3 operandGroup.path [70],
    numberDeclaration 4 operandGroup.path "Input" [70]
  ]
  repeatableGroups := [frame, targetGroup, operandGroup]
}

private def operandPath : SurfaceFieldPath := {
  base := .absolute
  groups := operandGroup.path
  field := "Input"
}

private def checked? :=
  (checkParallelNumericComputationClearingPlan
    model ["Plan"] 2 operandPath).toOption

private def world : World := { now := { epochMillis := 0 } }

private def rows : List RowAddr := [
  { group := 50, path := [1] },
  { group := 60, path := [1, 1] },
  { group := 70, path := [1] },
  { group := 50, path := [2] },
  { group := 60, path := [2, 1] },
  { group := 60, path := [1, 2] },
  { group := 70, path := [2] }
]

private def indexCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.str stored)
}

private def cleanIndexCells : List ClassifiedCellInput := [
  indexCell 1 [1, 1] "Alpha",
  indexCell 1 [1, 2] "Beta",
  indexCell 1 [2, 1] "Gamma",
  indexCell 3 [1] "Alpha",
  indexCell 3 [2] "Beta"
]

private def sourceWith (cells : List ClassifiedCellInput) :
    DocumentData := { instantiatedRows := rows, cells }

private def checkedDocument? : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" (sourceWith [])).toOption

private def preliminaryFor (cells : List ClassifiedCellInput) :
    Option (CheckedIndexPreliminary model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  let checked ←
    (checkDocument prepared "en_US" (sourceWith cells)).toOption
  checked.applyFullIndexPreliminary.toOption

private def markCoordinates?
    (cells : List ClassifiedCellInput)
    (side : ParallelComputationIndexSide) :
    Option (List (List Nat)) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  let marks ← (checked.invalidIndexMarks preliminary side).toOption
  pure (marks.map (·.coordinates))

/- Target instances come from physical rows at the deepest target scope, including blank-but-instantiated rows; unrelated group rows do not enter the projection. Document order is the Lean account's deterministic internal order, not a Kernel clearing-order claim. -/
example :
    (checked?.bind fun checked =>
      checkedDocument?.bind fun document =>
        (checked.targetEnvironments document).toOption) =
      some [
        [(50, 1), (60, 1)],
        [(50, 2), (60, 1)],
        [(50, 1), (60, 2)]
      ] := by
  native_decide

/- A clean checked index column emits no mark on either side. -/
example :
    markCoordinates? cleanIndexCells .target = some [] ∧
      markCoordinates? cleanIndexCells .operand = some [] := by
  native_decide

/- An unavailable target-path index marks only its frame, while the same clean document leaves the off-path operand side unmarked. -/
example :
    let targetInvalid := cleanIndexCells.filter fun input =>
      input.address != { field := 1, path := [2, 1] }
    markCoordinates? targetInvalid .target = some [[2]] ∧
      markCoordinates? targetInvalid .operand = some [] := by
  native_decide

/- An unavailable off-path operand index collapses to one root mark covering every target frame; the clean target-path column contributes nothing. -/
example :
    let operandInvalid := cleanIndexCells.filter fun input =>
      input.address != { field := 3, path := [2] }
    markCoordinates? operandInvalid .target = some [] ∧
      markCoordinates? operandInvalid .operand = some [[]] := by
  native_decide

/- Each checked index side derives its asymmetric common-prefix mark scope without a caller-supplied truncation width. -/
example :
    (checked?.map fun checked =>
      ((checked.markPlanFor .target).sharedScope,
        (checked.markPlanFor .operand).sharedScope)) =
      some ([50], []) := by
  native_decide

/- The checked scopes reproduce the observed discriminator: an on-path malformed key keeps frame siblings distinct, while an off-path malformed key covers both. -/
example :
    (checked?.bind fun checked => do
      let onPath ←
        (checked.markPlanFor .target).markForUnavailable
          (some .duplicateIndex) [(50, 1), (60, 1)] |>.toOption
      let offPath ←
        (checked.markPlanFor .operand).markForUnavailable
          (some .duplicateIndex) [(50, 1), (60, 1)] |>.toOption
      let onFirst ←
        (checked.markPlanFor .target).covers
          (← onPath) [(50, 1), (60, 1)] |>.toOption
      let onSecond ←
        (checked.markPlanFor .target).covers
          (← onPath) [(50, 2), (60, 1)] |>.toOption
      let offSecond ←
        (checked.markPlanFor .operand).covers
          (← offPath) [(50, 2), (60, 1)] |>.toOption
      pure (onFirst, onSecond, offSecond)) =
      some (true, false, true) := by
  native_decide

/- The ordinary non-starred operand and repeatable target determine both indexed groups and scopes without caller-supplied groups or a route bit. -/
example :
    (checked?.map fun checked =>
      (checked.groups.leftGroup.path,
        checked.groups.rightGroup.path,
        checked.targetDeclaration.repeatableScope,
        checked.operandDeclaration.repeatableScope)) =
      some (targetGroup.path, operandGroup.path, [50, 60], [70]) := by
  native_decide

/- A second ordinary field in the target's own indexed group is not a parallel route. -/
example :
    (match checkParallelNumericComputationClearingPlan model ["Plan"] 2 {
        base := .absolute
        groups := targetGroup.path
        field := "Peer"
      } with
    | .error error => some error
    | .ok _ => none) =
      some (.join (.incompatibleGroups targetGroup.path targetGroup.path)) := by
  native_decide

end A12Kernel.Conformance.ParallelComputationClearingPlan
