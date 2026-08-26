import A12Kernel.Elaboration.AddressedBooleanFirstFilledComputation

/-! # Exact-address repeatable Boolean `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedBooleanFirstFilledComputation

open A12Kernel

private def booleanField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .boolean }
}

private def source := booleanField 1 "Decision"
  ["Projects", "Choices"] [10, 20]

private def target := booleanField 2 "Selected"
  ["Projects", "Tasks"] [10, 30]

private def unrelated := booleanField 3 "Unrelated" ["Summary"] []

private def fixedTarget := booleanField 4 "Fixed" ["Summary"] []

private def confirmSource : FlatFieldDecl := {
  source with id := 5, name := "Confirmed", policy := { kind := .confirm }
}

private def nestedSource := booleanField 6 "NestedDecision"
  ["Projects", "Choices", "Details"] [10, 20, 40]

private def unboundTarget := booleanField 7 "UnboundSelected"
  ["OtherTasks"] [50]

private def rootSource := booleanField 8 "GlobalDecision"
  ["GlobalChoices"] [60]

private def model : FlatModel := {
  fields := [source, target, unrelated, fixedTarget, confirmSource, nestedSource,
    unboundTarget, rootSource]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 4 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3 },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 },
    { level := 40, path := ["Projects", "Choices", "Details"],
      repeatability := some 3 },
    { level := 50, path := ["OtherTasks"], repeatability := some 3 },
    { level := 60, path := ["GlobalChoices"], repeatability := some 3 }]
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

private def selfStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Tasks", starred := true }]
  field := target.name
}

private def absoluteSiblingStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Projects" },
    { name := "Choices", starred := true }]
  field := source.name
}

private def rootStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "GlobalChoices", starred := true }]
  field := rootSource.name
}

private def operation? :
    Option (CheckedAddressedBooleanFirstFilledComputation model) :=
  (checkAddressedBooleanFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked :
    Except AddressedBooleanFirstFilledComputationElabError
      (CheckedAddressedBooleanFirstFilledComputation model)) :
    Option AddressedBooleanFirstFilledComputationElabError :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The addressed boundary requires a repeatable Boolean target, one Boolean star axis, and no target self-read. -/
example :
    operation?.isSome = true ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects"] target.id (siblingStar source.name)) =
        some (.targetOutsideDeclaringGroup target.path ["Projects"]) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Choices"] confirmSource.id (siblingStar source.name)) =
        some (.targetKind confirmSource.path .confirm) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar confirmSource.name)) =
        some (.sourceKind confirmSource.path .confirm) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id nestedSiblingStar) =
        some (.sourceShape nestedSource.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["OtherTasks"] unboundTarget.id absoluteSiblingStar) =
        some (.sourceScope source.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id rootStar) =
        some (.sourceScope rootSource.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id selfStar) =
        some (.targetSelfReference target.id) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 10, path := [3] }, { group := 10, path := [4] },
    { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] },
    { group := 20, path := [4, 1] },
    { group := 30, path := [2, 1] }, { group := 30, path := [1, 2] },
    { group := 30, path := [4, 2] }, { group := 30, path := [1, 1] },
    { group := 30, path := [3, 1] }, { group := 30, path := [4, 1] },
    { group := 30, path := [3, 2] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := classifyStoredBooleanText stored
}

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def input? : Option (CheckedDocument model) :=
  document? [
    cell source.id [1, 1] "false",
    cell source.id [2, 1] "true",
    cell source.id [4, 1] "TRUE",
    cell target.id [1, 1] "false",
    cell target.id [1, 2] "true",
    cell target.id [3, 1] "true",
    cell target.id [4, 1] "false",
    cell unrelated.id [] "true"]

/- Each target row scans only its enclosing parent's sibling source rows. False remains a value, an empty sibling extent yields no value, and malformed content poisons only that parent. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.result))) = some [
      (address target.id [2, 1], .value true),
      (address target.id [1, 2], .value false),
      (address target.id [4, 2], .poison .booleanToken),
      (address target.id [1, 1], .value false),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .booleanToken),
      (address target.id [3, 2], .noValue)] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × Bool)
  changes : List (CellAddr × Bool)
  cleared : List CellAddr
  row11 : BooleanTargetState
  row12 : BooleanTargetState
  row21 : BooleanTargetState
  row31 : BooleanTargetState
  row32 : BooleanTargetState
  row41 : BooleanTargetState
  row42 : BooleanTargetState
  unrelatedState : BooleanTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "true",
    cell target.id [2, 1] "false",
    cell target.id [4, 1] "true",
    cell unrelated.id [] "false"]
  let result ← operation.executeResult input
    ([.booleanToken] : List FormalCause) |>.toOption
  let applied := result.applyToChecked destination
  pure {
    values := result.boolean.withoutErrors.map fun item =>
      (item.targetField, item.value)
    changes := result.boolean.withChanges.map fun item =>
      (item.targetField, item.value)
    cleared := result.boolean.cleared
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row31 := applied (address target.id [3, 1])
    row32 := applied (address target.id [3, 2])
    row41 := applied (address target.id [4, 1])
    row42 := applied (address target.id [4, 2])
    unrelatedState := applied (address unrelated.id [])
  }

/- Result classification uses immutable exact target state, then changed values and retained clears apply to a separate destination without disturbing unchanged or unrelated cells. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [2, 1], true),
      (address target.id [1, 2], false),
      (address target.id [1, 1], false)]
    changes := [
      (address target.id [2, 1], true),
      (address target.id [1, 2], false)]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    row11 := .presentValue true
    row12 := .presentValue false
    row21 := .presentValue true
    row31 := .presentEmpty
    row32 := .absent
    row41 := .presentEmpty
    row42 := .absent
    unrelatedState := .presentValue false
  } := by
  native_decide

end A12Kernel.Conformance.AddressedBooleanFirstFilledComputation
