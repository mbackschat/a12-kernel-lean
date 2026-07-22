import A12Kernel.Elaboration.StarNumber

/-! # Checked nested Number-star consumption locks -/

namespace A12Kernel.Conformance.StarNumberElaboration

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 20] }

private def note : FlatFieldDecl :=
  { amount with id := 8, name := "Note", policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [amount, note]
    repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"], repeatability := some 2 },
      { level := 10, path := ["Shop", "Sections"], repeatability := some 2 }] }

private def source (field : String := "Amount") (outerStar : Bool := true) :
    SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Shop" }, { name := "Sections", starred := outerStar },
      { name := "Items", starred := true }]
    field }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def standardRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] },
  { group := 20, path := [1, 2] }, { group := 10, path := [2] },
  { group := 20, path := [2, 1] }]

private def readAmount (environment : Env) (_ : FieldId) : RawCell :=
  match environment with
  | [(10, 1), (20, 1)] => .parsed (.num 1)
  | [(10, 1), (20, 2)] => .presentEmpty
  | [(10, 2), (20, 1)] => .parsed (.num 3)
  | _ => .empty

private inductive NumberCellSnapshot where
  | present (value : Rat)
  | empty
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

private def snapshotCell : ValueListCell .number → NumberCellSnapshot
  | .present value => .present value
  | .empty => .empty
  | .unknown cause => .unknown cause

private def cellsOf (authored : SurfaceStarFieldPath) (rows : List RowAddr)
    (outer : Env := []) (read : Env → FieldId → RawCell := readAmount) :=
  match elaborateStarNumberSource model amount.groupPath authored with
  | .error _ => none
  | .ok checked => match checked.resolvedValueSide (document rows) outer read with
      | .error _ => none
      | .ok side => some (side.cells.map snapshotCell, side.hasUninstantiatedTail)

/- The checked consumer preserves canonical nested order, emptiness, and the hierarchical tail. -/
example : cellsOf (source) standardRows = some (
    [.present 1, .empty, .present 3], true) := by
  native_decide

/- An unstarred outer axis is bound by identity before the inner star reopens. -/
example : cellsOf (source (outerStar := false)) standardRows [(10, 2)] =
    some ([.present 3], true) := by
  native_decide

/- Either an inner or outer over-capacity coordinate makes the selected Number cell formally unavailable. -/
example :
    let innerRows := standardRows ++ [{ group := 20, path := [1, 3] }]
    let outerRows := standardRows ++ [
      { group := 10, path := [3] }, { group := 20, path := [3, 1] }]
    cellsOf (source) innerRows (read := fun env _ =>
      if env == [(10, 1), (20, 3)] then .parsed (.num 9) else readAmount env amount.id) =
        some ([.present 1, .empty, .unknown .overRepetition, .present 3], true) ∧
    cellsOf (source (outerStar := false)) outerRows [(10, 3)] (read := fun env _ =>
      if env == [(10, 3), (20, 1)] then .parsed (.num 9) else readAmount env amount.id) =
        some ([.unknown .overRepetition], true) := by
  native_decide

/- General checked path admission remains kind-safe for the concrete Number consumer. -/
example :
    (match elaborateStarNumberSource model amount.groupPath (source "Note") with
    | .error (.fieldNotNumber path) => path == note.path
    | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.StarNumberElaboration
