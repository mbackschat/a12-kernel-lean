import A12Kernel.Elaboration.StarGroup

/-! # Checked terminal-repeatable group-star locks -/

namespace A12Kernel.Conformance.StarGroupElaboration

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Catalog", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 20] }

private def sections : RepeatableGroupDecl :=
  { level := 10, path := ["Shop", "Catalog", "Sections"], repeatability := some 2 }

private def items : RepeatableGroupDecl :=
  { level := 20, path := ["Shop", "Catalog", "Sections", "Items"], repeatability := some 3 }

private def model : FlatModel :=
  { fields := [amount], repeatableGroups := [items, sections] }

private def segment (name : String) (starred : Bool := false) : SurfaceStarGroupSegment :=
  { name, starred }

private def absoluteSource (catalogStar outerStar innerStar : Bool) : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [segment "Shop", segment "Catalog" catalogStar,
      segment "Sections" outerStar, segment "Items" innerStar] }

private def relativeSource (outerStar innerStar : Bool) : SurfaceStarGroupPath :=
  { base := .relative 2
    groups := [segment "Sections" outerStar, segment "Items" innerStar] }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def checkedOf (source : SurfaceStarGroupPath) (targetModel : FlatModel := model) :=
  elaborateStarredGroupSource targetModel amount.groupPath source

private def resultOf (source : SurfaceStarGroupPath) :=
  match checkedOf source with
  | .ok checked => some (checked.group.level, checked.path)
  | .error _ => none

private def errorOf (source : SurfaceStarGroupPath) (targetModel : FlatModel := model) :=
  match checkedOf source targetModel with
  | .ok _ => none
  | .error error => some error

private def errorFromDeclaringGroup (declaringGroup : GroupPath)
    (source : SurfaceStarGroupPath) :=
  match elaborateStarredGroupSource model declaringGroup source with
  | .ok _ => none
  | .error error => some error

private def countOf (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option Nat :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.rowCount (document rows) outer with
      | .ok count => some count
      | .error _ => none

private def outcomeOf (operator : StarredGroupFillQuantifier)
    (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option ValidationFillOutcome :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull operator (document rows) outer with
      | .ok outcome => some outcome
      | .error _ => none

private def countResultOf (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option FilledGroupCount :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.numberOfFilledGroups (document rows) outer with
      | .ok result => some result
      | .error _ => none

private def contextErrorOf (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option StarAddressingError :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.rowCount (document rows) outer with
      | .ok _ => none
      | .error error => some error

private def oneEmptyItem : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 20, path := [1, 1] }]

private def nestedRows : List RowAddr :=
  [{ group := 20, path := [2, 1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 2] }, { group := 10, path := [1] },
    { group := 20, path := [1, 1] }]

/- Checked lowering retains the terminal group and the exact first-star plan. -/
example :
    resultOf (relativeSource false true) = some (20,
      { axes := [{ level := 10, repeatability := some 2 },
          { level := 20, repeatability := some 3 }], firstStar := 1 }) ∧
    resultOf (relativeSource true true) = some (20,
      { axes := [{ level := 10, repeatability := some 2 },
          { level := 20, repeatability := some 3 }], firstStar := 0 }) := by
  native_decide

/- A created-but-empty terminal row is structural content: no cell read is involved. -/
example :
    countOf (absoluteSource false true true) [] = some 0 ∧
    countOf (absoluteSource false true true) oneEmptyItem = some 1 ∧
    outcomeOf .noGroupFilled (absoluteSource false true true) [] =
      some (.fired .omission) ∧
    outcomeOf .noGroupFilled (absoluteSource false true true) oneEmptyItem =
      some .falseOrUnknown ∧
    outcomeOf .atLeastOneGroupFilled (absoluteSource false true true) [] =
      some .falseOrUnknown ∧
    outcomeOf .atLeastOneGroupFilled (absoluteSource false true true) oneEmptyItem =
      some (.fired .value) := by
  native_decide

/- The numeric consumer shares the same row count, including the zero-row case. -/
example :
    countResultOf (absoluteSource false true true) [] = some (.value 0) ∧
    countResultOf (absoluteSource false true true) oneEmptyItem = some (.value 1) := by
  native_decide

/- Reopening both levels counts every terminal row in canonical topology, independent of storage order. -/
example :
    countOf (absoluteSource false true true) nestedRows = some 3 ∧
    countResultOf (absoluteSource false true true) nestedRows = some (.value 3) := by
  native_decide

/- Binding the outer level before reopening the terminal group counts only that parent's rows. -/
example :
    countOf (relativeSource false true) nestedRows [(10, 1)] = some 2 ∧
    countOf (relativeSource false true) nestedRows [(10, 2)] = some 1 := by
  native_decide

/- Sequential over-limit rows remain instantiated structural content; their separate diagnostic does not erase them. -/
example :
    let rows := [{ group := 10, path := [1] },
      { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
      { group := 20, path := [1, 3] }, { group := 20, path := [1, 4] }]
    countOf (absoluteSource false true true) rows = some 4 := by
  native_decide

/- Static and runtime topology failures remain fail-closed at their existing owners. -/
example :
    errorOf (absoluteSource true true true) =
      some (.path (.wildcardOnNonrepeatable ["Shop", "Catalog"])) ∧
    errorOf (relativeSource true false) =
      some (.path (.iterationBelowWildcard ["Shop", "Catalog", "Sections", "Items"])) ∧
    errorOf (relativeSource false false) =
      some (.path (.missingWildcard items.path)) ∧
    errorOf (absoluteSource false false true)
      { fields := [], repeatableGroups := [sections] } =
      some (.resolve (.unknownRepeatableGroup items.path)) := by
  native_decide

/- Caller-context invalidity remains distinct from an invalid group operand for both path bases. -/
example :
    errorFromDeclaringGroup [] (absoluteSource false true true) =
      some (.resolve (.invalidRuleGroup [])) ∧
    errorFromDeclaringGroup [] (relativeSource true true) =
      some (.resolve (.invalidRuleGroup [])) := by
  native_decide

example :
    let rows := [{ group := 10, path := [1] }, { group := 20, path := [1, 2] }]
    contextErrorOf (absoluteSource false true true) rows =
      some (.nonprefixRows 20 [1] [2]) := by
  native_decide

end A12Kernel.Conformance.StarGroupElaboration
