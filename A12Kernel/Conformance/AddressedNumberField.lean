import A12Kernel.Elaboration.AddressedNumberField

/-! # Addressed direct Number-field locks

The matrix separates exact-scale admission, empty zero, row-local value and poison, target rejection, source-relative result classification, and exact addresses.
-/

namespace A12Kernel.Conformance.AddressedNumberField

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Source"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def target : FlatFieldDecl := {
  source with
    id := 2
    name := "Target"
    numericTargetConstraints := { maximum := some (999 / 100) }
}

private def wrong : FlatFieldDecl := {
  source with id := 3, name := "Wrong", policy := { kind := .string }
}

private def outer : FlatFieldDecl := {
  source with id := 4, name := "Outer", groupPath := ["Order"], repeatableScope := []
}

private def siblingSource : FlatFieldDecl := {
  source with
    id := 6
    name := "Sibling"
    groupPath := ["Order", "Others"]
    repeatableScope := [20]
}

/-- A real declared group strictly below the target's own group, so the placement separator refuses
a genuine group rather than an invented path. -/
private def deeperSource : FlatFieldDecl := {
  source with id := 7, name := "DeeperSource", groupPath := ["Order", "Rows", "Deeper"]
}

private def scaleZero : FlatFieldDecl := {
  target with
    id := 5
    name := "ScaleZero"
    policy := { kind := .number { scale := 0, signed := true } }
    numericTargetConstraints := {}
}

private def model : FlatModel := {
  fields := [source, target, wrong, outer, siblingSource, scaleZero,
    deeperSource]
  repeatableGroups := [
    { level := 10, path := ["Order", "Rows"], repeatability := some 4 },
    { level := 20, path := ["Order", "Others"], repeatability := some 3 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def sibling (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := ["Others"], field }

private def operation? : Option (CheckedAddressedNumberField model) :=
  (checkAddressedNumberField model ["Order", "Rows"] target.id
    (bare "Source")).toOption

private def cell (field : FieldId) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored, raw }

private def decimalCell (field : FieldId) (row : Nat) (stored : String)
    (unscaled scale : Int) (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [row] }
  stored
  raw
  numericDecimal := some { unscaled, scale }
}

private def input? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range 4).map fun i => { group := 10, path := [i + 1] }
    cells
  }).toOption

private def result? (cells : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation?
  let input ← input? cells
  (operation.executeResult input (fun _ => ()) []).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

/- Exact source and target scales are part of checked authoring; wrong kind and unbound scope fail
separately. The **outer-scope** source is admitted: the placement requires only that the target's own
scope bind every repeatable level the source crosses, which the Kernel confirms by admitting an
outer-scope operand and refusing a sibling one. This is the shared placement's branch, so the other
one-source leaves assert admission alone rather than repeating the refusal. -/
example :
    operation?.isSome = true ∧
    (match checkAddressedNumberField model ["Order", "Rows"] target.id (bare "Wrong") with
      | .error (.sourceNotNumber path .string) => path == wrong.path
      | _ => false) = true ∧
    (match checkAddressedNumberField model ["Order", "Rows"] scaleZero.id (bare "Source") with
      | .error (.scaleMismatch 0 2) => true
      | _ => false) = true ∧
    (checkAddressedNumberField model ["Order", "Rows"] target.id
      (parent "Outer")).isOk = true ∧
    (match checkAddressedNumberField model ["Order", "Rows"] target.id
        (sibling "Sibling") with
      | .error (.placement (.scopeMismatch targetPath sourcePath)) =>
          targetPath == target.path && sourcePath == siblingSource.path
      | _ => false) = true := by
  native_decide

/- The shared numeric placement admits by containment, not group equality: an ancestor declaring group takes the repeatable target, a sibling group and a declared group strictly below it do not, and an unrepresentable declaring group is refused before containment can vacuously admit everything. -/
example :
    (checkAddressedNumberField model ["Order"] target.id (bare "Outer")).isOk = true ∧
    (match checkAddressedNumberField model ["Order", "Rows", "Deeper"] target.id
        (bare "DeeperSource") with
      | .error (.placement (.targetOutsideDeclaringGroup path declaringGroup)) =>
          path == target.path && declaringGroup == ["Order", "Rows", "Deeper"]
      | _ => false) = true ∧
    (match checkAddressedNumberField model ["Order", "Others"] target.id
        (bare "Sibling") with
      | .error (.placement (.targetOutsideDeclaringGroup path declaringGroup)) =>
          path == target.path && declaringGroup == ["Order", "Others"]
      | _ => false) = true ∧
    (match checkAddressedNumberField model [] target.id (bare "Source") with
      | .error (.placement (.target (.invalidRuleGroup group))) => group == []
      | _ => false) = true := by
  native_decide

/- The direct read retains empty-as-zero, exact row values, formal poison, target rejection, and source-relative change identity. -/
example :
    (do
      let view ← result? [
        cell source.id 2 "1.25" (.parsed (.num (5 / 4))),
        decimalCell target.id 2 "1.25" 125 2 (.parsed (.num (5 / 4))),
        cell source.id 3 "bad" (.rejected .malformed),
        cell target.id 3 "2.00" (.parsed (.num 2)),
        cell source.id 4 "12.34" (.parsed (.num (617 / 50)))
      ]
      pure (view.withChanges.map fun entry => (entry.targetField, entry.value),
        view.cleared, view.withErrors)) =
      some (
        [(addr target.id 1, stored 0 0)],
        [addr target.id 3],
        [{
          targetField := addr target.id 4
          attempted := stored 1234 2
          cause := .aboveMaximum
        }]) := by
  native_decide

private def outerOperation? : Option (CheckedAddressedNumberField model) :=
  (checkAddressedNumberField model ["Order", "Rows"] target.id
    (parent "Outer")).toOption

private def outerOutcomes? (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← outerOperation?
  let input ← input? cells
  let executed ← (operation.execute input).toOption
  pure (executed.map fun entry => (entry.targetField, entry.outcome))

/- An outer-scope source is read at its **own** path, so one root cell reaches every target row. This
is what the widening buys and what borrowing the target's path would break: addressing `Outer` at
`[1]…[4]` would find no cell and read every row as empty. -/
example :
    outerOutcomes? [
      { address := { field := outer.id, path := [] }, stored := "7.50"
        raw := .parsed (.num (15 / 2)) }
    ] = some [
      (addr target.id 1, .accepted (stored 75 1)),
      (addr target.id 2, .accepted (stored 75 1)),
      (addr target.id 3, .accepted (stored 75 1)),
      (addr target.id 4, .accepted (stored 75 1))
    ] := by
  native_decide

/- The same source read at its own path keeps its own emptiness and its own formal invalidity, which
every row then inherits rather than only the row that happens to share its index. -/
example :
    outerOutcomes? [] = some [
      (addr target.id 1, .accepted (stored 0 0)),
      (addr target.id 2, .accepted (stored 0 0)),
      (addr target.id 3, .accepted (stored 0 0)),
      (addr target.id 4, .accepted (stored 0 0))
    ] ∧
    outerOutcomes? [
      { address := { field := outer.id, path := [] }, stored := "bad"
        raw := .rejected .malformed }
    ] = some [
      (addr target.id 1, .inheritedPoison .malformed),
      (addr target.id 2, .inheritedPoison .malformed),
      (addr target.id 3, .inheritedPoison .malformed),
      (addr target.id 4, .inheritedPoison .malformed)
    ] := by
  native_decide

end A12Kernel.Conformance.AddressedNumberField
