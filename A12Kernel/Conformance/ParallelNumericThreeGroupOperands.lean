import A12Kernel.Elaboration.ParallelNumericDirectRunResult

/-! # Parallel Number three-group operand locks

These cases add one independently indexed operand group to the isolated Number run. They distinguish the Kernel's n-way key union plus existing-target gate from both pairwise-only evaluation and target creation for an operand-only key.
-/

namespace A12Kernel.Conformance.ParallelNumericThreeGroupOperands

open A12Kernel

private def indexDeclaration (id : FieldId) (path : GroupPath)
    (level : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name := "Key"
  policy := { kind := .string }
  repeatableScope := [level]
}

private def numberDeclaration (id : FieldId) (path : GroupPath)
    (name : String) (level : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [level]
}

private def stringDeclaration (id : FieldId) (path : GroupPath)
    (name : String) (level : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name
  policy := { kind := .string }
  repeatableScope := [level]
}

private def targetGroup : RepeatableGroupDecl := {
  level := 1
  path := ["Plan", "Target"]
  repeatability := some 2
  indexField := some 1
}

private def inputGroup : RepeatableGroupDecl := {
  level := 3
  path := ["Plan", "Input"]
  repeatability := some 2
  indexField := some 3
}

private def offsetGroup : RepeatableGroupDecl := {
  level := 5
  path := ["Plan", "Offset"]
  repeatability := some 2
  indexField := some 5
}

/-- Shared three-group model for focused multi-group expression and guard locks. -/
def model : FlatModel := {
  fields := [
    indexDeclaration 1 targetGroup.path 1,
    numberDeclaration 2 targetGroup.path "Result" 1,
    indexDeclaration 3 inputGroup.path 3,
    numberDeclaration 4 inputGroup.path "Amount" 3,
    indexDeclaration 5 offsetGroup.path 5,
    numberDeclaration 6 offsetGroup.path "Amount" 5,
    stringDeclaration 7 offsetGroup.path "Flag" 5,
    numberDeclaration 8 targetGroup.path "Seed" 1
  ]
  repeatableGroups := [targetGroup, inputGroup, offsetGroup]
}

/-- Anchor Number operand path in the first off-target indexed group. -/
def inputPath : SurfaceFieldPath := {
  base := .absolute
  groups := inputGroup.path
  field := "Amount"
}

/-- Number operand path in the second off-target indexed group. -/
def offsetPath : SurfaceFieldPath := {
  base := .absolute
  groups := offsetGroup.path
  field := "Amount"
}

private def targetPath : SurfaceFieldPath := {
  base := .absolute
  groups := targetGroup.path
  field := "Result"
}

/-- Ordinary Number source used to distinguish a genuine three-target dependency chain. -/
def seedPath : SurfaceFieldPath := {
  base := .absolute
  groups := targetGroup.path
  field := "Seed"
}

private def expression : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field inputPath))
    (.atom (.field offsetPath))

private def checked? :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 inputPath expression none).toOption

/-- Two physically instantiated rows in each participating indexed group. -/
def rows : List RowAddr := [
  { group := 1, path := [1] },
  { group := 1, path := [2] },
  { group := 3, path := [1] },
  { group := 3, path := [2] },
  { group := 5, path := [1] },
  { group := 5, path := [2] }
]

/-- One clean exact-String index cell. -/
def indexCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.str stored)
}

/-- One typed Number placement; target cells retain source identity for result classification. -/
def numberCell (field : FieldId) (path : List Nat)
    (stored : StoredNumber) : ClassifiedCellInput := {
  address := { field, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
  numericDecimal := some {
    unscaled := stored.unscaled
    scale := stored.scale
  }
}

/-- Clean columns and Number operands for the two target keys plus one operand-only key. -/
def cleanCells : List ClassifiedCellInput := [
  indexCell 1 [1] "Alpha",
  indexCell 1 [2] "Beta",
  indexCell 3 [1] "Alpha",
  indexCell 3 [2] "Beta",
  indexCell 5 [1] "Alpha",
  indexCell 5 [2] "Gamma",
  numberCell 4 [1] { unscaled := 10, scale := 0 },
  numberCell 4 [2] { unscaled := 20, scale := 0 },
  numberCell 6 [1] { unscaled := 1, scale := 0 },
  numberCell 6 [2] { unscaled := 99, scale := 0 },
  numberCell 8 [1] { unscaled := 2, scale := 0 },
  numberCell 8 [2] { unscaled := 3, scale := 0 }
]

private def invalidThird : List ClassifiedCellInput :=
  (cleanCells.filter fun cell =>
    cell.address != { field := 5, path := [2] }) ++ [
      numberCell 2 [1] { unscaled := 7, scale := 0 },
      numberCell 2 [2] { unscaled := 8, scale := 0 }
    ]

private def world : World := { now := { epochMillis := 0 } }

/-- Construct the checked preliminary shared by the focused three-group cases. -/
def preliminaryFor (cells : List ClassifiedCellInput) :
    Option (CheckedIndexPreliminary model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  let document ←
    (checkDocument prepared "en_US" {
      instantiatedRows := rows
      cells
    }).toOption
  document.applyFullIndexPreliminary.toOption

private def outcomes? (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  (checked.execute preliminary).toOption

private def result? (cells : List ClassifiedCellInput) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  (checked.executeResult preliminary (fun _ => true) []).toOption

/- The two expression groups retain exactly one route each: the anchor plus one additional route. -/
example :
    checked?.map (·.additionalRoutes.length) = some 1 := by
  native_decide

/- The explicit anchor must occur in the expression's indexed group; it cannot add an otherwise unread group to iteration and invalidity marking. -/
example :
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 inputPath (.atom (.field offsetPath)) none with
    | .error error => some error
    | .ok _ => none) =
      some .expressionNotLimitedToOperand := by
  native_decide

/- Current checked construction rejects the target itself as anchor, expression atom, or guard leaf; the finite plan does not promote these cases into a universal exclusion theorem. -/
example :
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 targetPath (.atom (.field targetPath)) none with
    | .error error => some error
    | .ok _ => none) =
      some (.route (.join
        (.incompatibleGroups targetGroup.path targetGroup.path))) ∧
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 inputPath (.atom (.field targetPath)) none with
    | .error error => some error
    | .ok _ => none) =
      some .expressionNotLimitedToOperand ∧
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 inputPath (.atom (.field inputPath))
          (some (.fieldFilled 2)) with
    | .error error => some error
    | .ok _ => none) =
      some .guardNotLimitedToOperand := by
  native_decide

/- The operand-only `Gamma` key does not create a target row; the clean target-only `Beta` key reads the unmatched third operand as zero. -/
example :
    (outcomes? cleanCells).map (·.map (·.outcome)) =
      some [
        .accepted { unscaled := 11, scale := 0 },
        .accepted { unscaled := 20, scale := 0 }
      ] := by
  native_decide

/- One invalid third-group index column suppresses all root-frame outcomes and clears only source-filled existing targets. -/
example :
    (outcomes? invalidThird).map (·.map (·.outcome)) = some [] ∧
      (result? invalidThird).map (·.cleared) =
        some [
          { field := 2, path := [1] },
          { field := 2, path := [2] }
        ] := by
  native_decide

end A12Kernel.Conformance.ParallelNumericThreeGroupOperands
