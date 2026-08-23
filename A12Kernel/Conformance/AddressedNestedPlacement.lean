import A12Kernel.Elaboration.AddressedNumberField

/-! # Addressed placement over a nested repeatable target

A two-level computed target is where the operand-scope rule earns its shape. Each operand is read
at its **own** path inside the current leaf row, so a form-level operand reaches every leaf, an
operand one level up reaches only the leaves of its own enclosing row, and a leaf operand stays
row-local. Getting this wrong is a wrong value rather than a refusal, which is why the correlating
middle case carries its own separating rows rather than sharing the outer one's.

The direct Number leaf is the vehicle because the placement, not the leaf, owns this behaviour.
-/

namespace A12Kernel.Conformance.AddressedNestedPlacement

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath
  repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }
}

private def rootBase := number 1 "RootBase" ["Probe"] []
private def rowBase := number 2 "RowBase" ["Probe", "Rows"] [10]
private def leafSource :=
  number 3 "LeafSource" ["Probe", "Rows", "Inner"] [10, 20]
private def leafTarget :=
  number 4 "LeafTarget" ["Probe", "Rows", "Inner"] [10, 20]

private def model : FlatModel := {
  fields := [rootBase, rowBase, leafSource, leafTarget]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Rows"], repeatability := some 3 },
    { level := 20, path := ["Probe", "Rows", "Inner"], repeatability := some 3 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def grandparent (field : String) : SurfaceFieldPath :=
  { base := .relative 2, groups := [], field }

private def leafGroup : GroupPath := ["Probe", "Rows", "Inner"]

private def operation? (source : SurfaceFieldPath) :
    Option (CheckedAddressedNumberField model) :=
  (checkAddressedNumberField model leafGroup leafTarget.id source).toOption

/- The leaf target's scope binds both enclosing levels, so an operand at any of the three scopes is
admitted, while an operand at the leaf scope feeding the **row** target's level is not — that target
is not repeatable-at-leaf and the operand crosses a level it does not bind. -/
example :
    (operation? (grandparent "RootBase")).isSome = true ∧
      (operation? (parent "RowBase")).isSome = true ∧
      (operation? (bare "LeafSource")).isSome = true ∧
      (match checkAddressedNumberField model ["Probe", "Rows"] rowBase.id
          { base := .relative 0, groups := ["Inner"], field := "LeafSource" } with
        | .error (.placement (.scopeMismatch targetPath sourcePath)) =>
            targetPath == rowBase.path && sourcePath == leafSource.path
        | _ => false) = true := by
  native_decide

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
    { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def cell (field : FieldId) (path : List Nat) (stored : String)
    (amount : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw := .parsed (.num amount) }

private def input? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def outcomes? (source : SurfaceFieldPath)
    (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation? source
  let document ← input? cells
  let executed ← (operation.execute document).toOption
  pure (executed.map fun entry => (entry.targetField, entry.outcome))

private def leaf (outer inner : Nat) : CellAddr :=
  { field := leafTarget.id, path := [outer, inner] }

private def stored (unscaled : Int) : StoredNumber := { unscaled, scale := 0 }

/- One form-level operand reaches every leaf: the target iterates its own two-level scope while the
operand resolves at the document root. -/
example :
    outcomes? (grandparent "RootBase") [cell rootBase.id [] "7" 7] = some [
      (leaf 1 1, .accepted (stored 7)),
      (leaf 1 2, .accepted (stored 7)),
      (leaf 2 1, .accepted (stored 7)),
      (leaf 2 2, .accepted (stored 7))
    ] := by
  native_decide

/- An operand one level up reaches exactly the leaves of **its own** enclosing row. Two distinct
outer values separate this from both wrong accounts: borrowing the leaf path would read `RowBase` at
a two-element address and find nothing, and reading only the first row would give every leaf `11`. -/
example :
    outcomes? (parent "RowBase")
      [cell rowBase.id [1] "11" 11, cell rowBase.id [2] "22" 22] = some [
      (leaf 1 1, .accepted (stored 11)),
      (leaf 1 2, .accepted (stored 11)),
      (leaf 2 1, .accepted (stored 22)),
      (leaf 2 2, .accepted (stored 22))
    ] := by
  native_decide

/- A leaf operand stays row-local, so each of the four leaves keeps its own value and an unplaced
leaf substitutes the real zero rather than borrowing a sibling's. -/
example :
    outcomes? (bare "LeafSource")
      [cell leafSource.id [1, 1] "1" 1, cell leafSource.id [1, 2] "2" 2,
        cell leafSource.id [2, 2] "4" 4] = some [
      (leaf 1 1, .accepted (stored 1)),
      (leaf 1 2, .accepted (stored 2)),
      (leaf 2 1, .accepted (stored 0)),
      (leaf 2 2, .accepted (stored 4))
    ] := by
  native_decide

/- An enclosing operand's own formal invalidity reaches every leaf beneath it and no others, which
is the poison direction of the same correlation. -/
example :
    outcomes? (parent "RowBase") [
      { address := { field := rowBase.id, path := [1] }, stored := "bad"
        raw := .rejected .malformed },
      cell rowBase.id [2] "22" 22
    ] = some [
      (leaf 1 1, .inheritedPoison .malformed),
      (leaf 1 2, .inheritedPoison .malformed),
      (leaf 2 1, .accepted (stored 22)),
      (leaf 2 2, .accepted (stored 22))
    ] := by
  native_decide

end A12Kernel.Conformance.AddressedNestedPlacement
