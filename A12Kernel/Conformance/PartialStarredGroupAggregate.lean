import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.CheckedDocument

/-! # A starred group operand's partial-validation extent

Under partial validation a field-expanding aggregate over a starred group is evaluable exactly when
every field the group contains passes the extent gate its own starred field would. The group path is
not the target: field identifiers alone settle the extent, an identifier on a descendant group
covers the fields below it, and concrete rows beside a field wildcard are encompassed by it. Every
coverage below is a row of the peer's first `kf464` table, whose `Lines*` column this locks on `Sum`
and `MaxValue` ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-kf464-partial-group-extent)).
-/

namespace A12Kernel.Conformance.PartialStarredGroupAggregate

open A12Kernel

private def number : FieldPolicy := { kind := .number { scale := 0, signed := false } }

/-- `Batches` (max 4) of a `Lot` and a fixed `Seal` of a `Code` and a Number `Weight`, and `Lines`
    (max 3) of two Numbers, as the peer's fixture declares them. -/
private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Item", "Batches"], name := "Lot", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 2, groupPath := ["Item", "Batches", "Seal"], name := "Code",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 3, groupPath := ["Item", "Batches", "Seal"], name := "Weight", policy := number,
        repeatableScope := [10] },
      { id := 4, groupPath := ["Item", "Lines"], name := "Qty", policy := number,
        repeatableScope := [20] },
      { id := 5, groupPath := ["Item", "Lines"], name := "Price", policy := number,
        repeatableScope := [20] }]
    repeatableGroups := [
      { level := 10, path := ["Item", "Batches"], repeatability := some 4 },
      { level := 20, path := ["Item", "Lines"], repeatability := some 3 }] }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def cell (field : FieldId) (row : Nat) (value : Nat) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored := toString value, raw := .parsed (.num value) }

private def text (field : FieldId) (row : Nat) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored := "A", raw := .parsed (.str "A") }

/-- Two rows of each group, every field filled but `Lot`. -/
private def document? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1] }, { group := 20, path := [2] }]
    cells := [text 2 1, text 2 2, cell 3 1 1, cell 3 2 1,
      cell 4 1 3, cell 4 2 4, cell 5 1 5, cell 5 2 6] }).toOption

private def linesSource? : Option (CheckedNumberEntitySource model) :=
  (elaborateNumberEntitySource model ["Item"]
    { first := .starredGroup { base := .absolute, groups :=
        [{ name := "Item" }, { name := "Lines", starred := true }] }
      rest := [] }).toOption

/-- Every repetition of one field or group. -/
private def every (path : List String) : RelevantEntityPattern :=
  RelevantEntityPattern.allInstances path

/-- One concrete row of the repeatable second segment. -/
private def atRow (path : List String) (row : Nat) : RelevantEntityPattern :=
  { path, indices := path.mapIdx fun index _ => if index == 1 then .concrete row else .all }

private def lot := ["Item", "Batches", "Lot"]
private def code := ["Item", "Batches", "Seal", "Code"]
private def weight := ["Item", "Batches", "Seal", "Weight"]
private def qty := ["Item", "Lines", "Qty"]
private def price := ["Item", "Lines", "Price"]
private def bothRows (path : List String) := [atRow path 1, atRow path 2]

/-- The first table's seven coverages, in its order. -/
private def coverages : List (List RelevantEntityPattern) :=
  [ [lot, code, weight, qty, price].map every,
    [code, weight, qty].map every,
    [every ["Item", "Batches"], every ["Item", "Lines"]],
    [every ["Item", "Batches", "Seal"], every lot, every qty, every price],
    [lot, code, weight, qty, price].map every ++
      bothRows ["Item", "Batches"] ++ bothRows ["Item", "Lines"],
    bothRows ["Item", "Batches"] ++ bothRows ["Item", "Lines"],
    bothRows lot ++ bothRows qty ++ [code, weight, price].map every ]

private def partial? (op : NumericAggregateOp) (entities : List RelevantEntityPattern) :
    Option PartialValidationNumberAggregateResult := do
  let source ← linesSource?
  let document ← document?
  (source.evaluateCheckedDocumentPartialAggregate op document [] (.partialSet entities)).toOption

/-- The same fold through a call-local view that reads the immutable cells unchanged. -/
private def partialView? (op : NumericAggregateOp) (entities : List RelevantEntityPattern) :
    Option PartialValidationNumberAggregateViewResult := do
  let source ← linesSource?
  let document ← document?
  (source.evaluatePartialViewAggregate op document [] (.partialSet entities)
    fun environment field => do
      pure (some (← document.addressedCell environment field).cell)).toOption

private def evaluable : Option PartialValidationNumberAggregateResult → Bool
  | some (.evaluated _) => true
  | _ => false

/- The column reads fires, silent, fires, fires, fires, silent, silent on both carriers. The first
   coverage names no identifier on the group path and still settles it, which a gate aimed at the
   group path gets wrong; the second leaves `Price` uncovered, which a gate satisfied by some field
   gets wrong; the last covers `Qty` concretely in every held row, which a gate counting covered
   cells gets wrong. -/
example :
    coverages.map (fun entities => evaluable (partial? .sum entities)) =
      [true, false, true, true, true, false, false] ∧
    coverages.map (fun entities => evaluable (partial? .maximum entities)) =
      [true, false, true, true, true, false, false] := by
  native_decide

private def partialValueCount? (entities : List RelevantEntityPattern) :
    Option PartialValidationNumberAggregateResult := do
  let source ← linesSource?
  let document ← document?
  (source.evaluateCheckedDocumentPartialValueCount 4 document [] (.partialSet entities)).toOption

/- `NumberOfValueInFields(4 In Lines*)` reads the same column. Its per-field gate is the existential
   one its starred field takes, which this table cannot tell from the all-rows gate: the fifth
   coverage is the only one naming a concrete row beside a field wildcard, and there the wildcard
   encompasses the row under either gate. -/
example :
    coverages.map (fun entities => evaluable (partialValueCount? entities)) =
      [true, false, true, true, true, false, false] := by
  native_decide

/- An evaluable extent answers the full-validation value, with the uncovered third `Lines` row still
   free to grow it, and the call-local view route agrees with the checked-document one. -/
example :
    partial? .sum (coverages.headD []) =
      some (.evaluated (.value 18 { canGrow := true, canShrink := false })) ∧
    (coverages.map fun entities => partialView? .maximum entities) =
      coverages.map fun entities => (partial? .maximum entities).map .result := by
  native_decide

end A12Kernel.Conformance.PartialStarredGroupAggregate
