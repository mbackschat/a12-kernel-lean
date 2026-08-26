import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation

/-! # Repeatable Enumeration `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedEnumerationFirstFilledComputation

open A12Kernel

private def targetDomain : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
}

private def incompatibleDomain : EnumerationDeclaration := {
  storedTokens := ["A", "C"]
}

private def enumerationField (id : FieldId) (name : String)
    (groupPath : GroupPath) (repeatableScope : List RepeatableLevel)
    (domain : EnumerationDeclaration := targetDomain) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope
  policy := { kind := .enumeration }
  enumeration := some domain
}

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (repeatableScope : List RepeatableLevel) :
    FlatFieldDecl := {
  id, name, groupPath, repeatableScope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def target := enumerationField 1 "Target" ["Form", "Rows"] [10]
private def source := enumerationField 2 "Source" ["Form", "Rows", "Items"] [10, 20]
private def incompatible := enumerationField 3 "Incompatible"
  ["Form", "Rows", "Items"] [10, 20] incompatibleDomain
private def limit := numberField 4 "Limit" ["Form", "Rows"] [10]
private def gate := numberField 5 "Gate" ["Form", "Rows", "Items"] [10, 20]
private def unrelated := enumerationField 6 "Unrelated" ["Form"] []
private def rootTarget := enumerationField 7 "RootTarget" ["Form"] []
private def directA := enumerationField 8 "DirectA" ["Form", "Rows"] [10]
private def directB := enumerationField 9 "DirectB" ["Form", "Rows"] [10]
private def nestedTarget := enumerationField 11 "NestedTarget"
  ["Form", "Rows", "Items"] [10, 20]
private def nestedDirectA := enumerationField 12 "NestedDirectA"
  ["Form", "Rows", "Items"] [10, 20]
private def nestedDirectB := enumerationField 13 "NestedDirectB"
  ["Form", "Rows", "Items"] [10, 20]

private def model : FlatModel := {
  fields := [target, source, incompatible, limit, gate, unrelated, rootTarget,
    directA, directB, nestedTarget, nestedDirectA, nestedDirectB]
  repeatableGroups := [{
    level := 10, path := ["Form", "Rows"], repeatability := some 3
  }, {
    level := 20, path := ["Form", "Rows", "Items"], repeatability := some 3
  }]
}

private def absoluteStar (field : String) (outerStar : Bool := false) :
    SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Form" },
    { name := "Rows", starred := outerStar },
    { name := "Items", starred := true }]
  field
}

private def targetStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Form" }, { name := "Rows", starred := true }]
  field := "Target"
}

private def numberRef (origin : HavingOrigin) (groups : List String)
    (field : String) : SurfaceHavingNumberRef := {
  origin
  field := { base := .absolute, groups, field }
}

private def selectedByLimit : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    (numberRef .inner ["Form", "Rows", "Items"] "Gate")
    (numberRef .outer ["Form", "Rows"] "Limit")

private def firstFilled (path : SurfaceStarFieldPath)
    (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceEnumerationFirstFilledSource := {
  first := .star path .stored having
  rest := []
}

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def parent (name : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field := name }

private def directFirstFilledAt (first second : SurfaceFieldPath) :
    SurfaceEnumerationFirstFilledSource := {
  first := .field (.direct first)
  rest := [.field (.direct second)]
}

private def directFirstFilled (first second : String) :
    SurfaceEnumerationFirstFilledSource :=
  directFirstFilledAt (bare first) (bare second)

private def operation? :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
    target.id (firstFilled (absoluteStar "Source"))).toOption

private def filteredOperation? :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
    target.id (firstFilled (absoluteStar "Source") (some selectedByLimit))).toOption

private def directOperation? :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
    target.id (directFirstFilled "DirectA" "DirectB")).toOption

private def nestedDirectOperation? :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model
    ["Form", "Rows", "Items"] nestedTarget.id
    (directFirstFilled "NestedDirectA" "NestedDirectB")).toOption

private def enclosingDirectOperation? :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model
    ["Form", "Rows", "Items"] nestedTarget.id
    (directFirstFilledAt (parent "DirectA") (parent "DirectB"))).toOption

private def errorOf (targetField : FieldId) (declaringGroup : GroupPath)
    (authored : SurfaceEnumerationFirstFilledSource) :
    Option AddressedEnumerationFirstFilledComputationElabError :=
  match checkAddressedEnumerationFirstFilledComputation model declaringGroup
      targetField authored with
  | .ok _ => none
  | .error cause => some cause

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def cell (field : FlatFieldDecl) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := { field := field.id, path }
  stored
  raw
}

private def document? (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def twoParents : List RowAddr := [
  row 10 [1], row 10 [2],
  row 20 [1, 1], row 20 [1, 2], row 20 [2, 1], row 20 [2, 2]]

private def outcomes? (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) :
    Option (List (CellAddr × TokenComputationResult)) := do
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun outcome => (outcome.targetField, outcome.result))

private structure ApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  row1 : StringTargetState
  row2 : StringTargetState
  unrelated : StringTargetState
  deriving Repr, DecidableEq

private def applicationSummary? (input destination : CheckedDocument model) :
    Option ApplicationSummary := do
  let operation ← operation?
  let result ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.string.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.text)
    changes := result.string.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    cleared := result.string.cleared
    row1 := applied { field := target.id, path := [1] }
    row2 := applied { field := target.id, path := [2] }
    unrelated := applied { field := unrelated.id, path := [] }
  }

private structure NestedApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  row11 : StringTargetState
  row21 : StringTargetState
  deriving Repr, DecidableEq

private def nestedApplicationSummary? (input destination : CheckedDocument model) :
    Option NestedApplicationSummary := do
  let operation ← nestedDirectOperation?
  let result ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.string.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.text)
    changes := result.string.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    row11 := applied { field := nestedTarget.id, path := [1, 1] }
    row21 := applied { field := nestedTarget.id, path := [2, 1] }
  }

/- The repeatable target accepts a child-star source, while root targets, incompatible projections, and a target read through a reopened star remain excluded. -/
example : operation?.isSome = true ∧ filteredOperation?.isSome = true ∧
    errorOf rootTarget.id ["Form"] (firstFilled (absoluteStar "Source" true)) =
      some (.target (.targetNotRepeatable rootTarget.path)) ∧
    errorOf target.id ["Form", "Rows"]
      (firstFilled (absoluteStar "Incompatible")) =
        some (.sourceIncompatible incompatible.path target.path) ∧
    errorOf target.id ["Form", "Rows"] (firstFilled targetStar) =
      some (.targetSelfReference target.id) := by
  native_decide

/- Direct operands at the target's own repeatable scope are admitted and read independently in each target row. -/
example : directOperation?.isSome = true ∧ (do
    let operation ← directOperation?
    let input ← document? [row 10 [1], row 10 [2]] [
      cell directB [1] "B" (.parsed (.enum "B")),
      cell directA [2] "A" (.parsed (.enum "A")),
      cell directB [2] "B" (.parsed (.enum "B"))]
    outcomes? operation input) = some [
      ({ field := target.id, path := [1] }, .value "B"),
      ({ field := target.id, path := [2] }, .value "A")] := by
  native_decide

/- A two-level target also admits direct operands one level up and fans each parent-local selection only to that parent's leaves. -/
example : enclosingDirectOperation?.isSome = true ∧ (do
    let operation ← enclosingDirectOperation?
    let input ← document? [
      row 10 [1], row 10 [2],
      row 20 [1, 1], row 20 [1, 2], row 20 [2, 1]] [
      cell directB [1] "B" (.parsed (.enum "B")),
      cell directA [2] "A" (.parsed (.enum "A"))]
    outcomes? operation input) = some [
      ({ field := nestedTarget.id, path := [1, 1] }, .value "B"),
      ({ field := nestedTarget.id, path := [1, 2] }, .value "B"),
      ({ field := nestedTarget.id, path := [2, 1] }, .value "A")] := by
  native_decide

/- Each parent row scans only its own children in authored order; an empty prefix reaches the later token, while poison remains local to the other exact target address. -/
example : (do
    let operation ← operation?
    let input ← document? twoParents [
      cell source [1, 2] "B" (.parsed (.enum "B")),
      cell source [2, 1] "C" (.parsed (.enum "C")),
      cell source [2, 2] "A" (.parsed (.enum "A"))]
    outcomes? operation input) = some [
      ({ field := target.id, path := [1] }, .value "B"),
      ({ field := target.id, path := [2] }, .poison .declaredConstraint)] := by
  native_decide

/- Two-level target coordinates remain distinct through result classification and separate-destination application. -/
example : (do
    let rows := [row 10 [1], row 10 [2], row 20 [1, 1], row 20 [2, 1]]
    let input ← document? rows [
      cell nestedTarget [1, 1] "B" (.parsed (.enum "B")),
      cell nestedTarget [2, 1] "A" (.parsed (.enum "A")),
      cell nestedDirectB [1, 1] "B" (.parsed (.enum "B")),
      cell nestedDirectA [2, 1] "B" (.parsed (.enum "B"))]
    let destination ← document? rows [
      cell nestedTarget [1, 1] "A" (.parsed (.enum "A")),
      cell nestedTarget [2, 1] "A" (.parsed (.enum "A"))]
    nestedApplicationSummary? input destination) = some {
      values := [
        ({ field := nestedTarget.id, path := [1, 1] }, "B"),
        ({ field := nestedTarget.id, path := [2, 1] }, "B")]
      changes := [({ field := nestedTarget.id, path := [2, 1] }, "B")]
      row11 := .presentValue ⟨"A", by decide⟩
      row21 := .presentValue ⟨"B", by decide⟩
    } := by
  native_decide

/- The checked resolving filter reads inner and outer cells per parent rather than selecting one global child sequence. -/
example : (do
    let operation ← filteredOperation?
    let input ← document? twoParents [
      cell limit [1] "1" (.parsed (.num 1)),
      cell limit [2] "2" (.parsed (.num 2)),
      cell gate [1, 1] "0" (.parsed (.num 0)),
      cell gate [1, 2] "1" (.parsed (.num 1)),
      cell gate [2, 1] "2" (.parsed (.num 2)),
      cell gate [2, 2] "0" (.parsed (.num 0)),
      cell source [1, 1] "A" (.parsed (.enum "A")),
      cell source [1, 2] "B" (.parsed (.enum "B")),
      cell source [2, 1] "A" (.parsed (.enum "A")),
      cell source [2, 2] "B" (.parsed (.enum "B"))]
    outcomes? operation input) = some [
      ({ field := target.id, path := [1] }, .value "B"),
      ({ field := target.id, path := [2] }, .value "A")] := by
  native_decide

/- Source-relative unchanged classification stays inert against a separate destination, while the other row's clear and unrelated state apply independently. -/
example : (do
    let input ← document? twoParents [
      cell target [1] "B" (.parsed (.enum "B")),
      cell target [2] "A" (.parsed (.enum "A")),
      cell source [1, 2] "B" (.parsed (.enum "B")),
      cell source [2, 1] "C" (.parsed (.enum "C"))]
    let destination ← document? [row 10 [1], row 10 [2]] [
      cell target [1] "A" (.parsed (.enum "A")),
      cell target [2] "B" (.parsed (.enum "B")),
      cell unrelated [] "A" (.parsed (.enum "A"))]
    applicationSummary? input destination) = some {
      values := [({ field := target.id, path := [1] }, "B")]
      changes := []
      cleared := [{ field := target.id, path := [2] }]
      row1 := .presentValue ⟨"A", by decide⟩
      row2 := .presentEmpty
      unrelated := .presentValue ⟨"A", by decide⟩
    } := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationFirstFilledComputation
