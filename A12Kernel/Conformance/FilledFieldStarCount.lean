import A12Kernel.Elaboration.FilledFieldStarCount
import A12Kernel.Elaboration.NumericAggregate.Entities

/-! # Capacity-bounded starred filled-field counts

The exact single-level over-repetition probe separates the star evaluation domain from the checked document's complete formal-cell view. Both `Sum` and `NumberOfFilledFields` must ignore the over-limit row while ordinary in-cap formal failures remain observable.
-/

namespace A12Kernel

private def premium : FlatFieldDecl :=
  { id := 2
    groupPath := ["Policy", "Coverages"]
    name := "Premium"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [premium]
    repeatableGroups := [{
      level := 10
      path := ["Policy", "Coverages"]
      repeatability := some 2 }] }

private def starPath : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Policy" },
      { name := "Coverages", starred := true }]
    field := "Premium" }

private def starredGroupPath : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [
      { name := "Policy" },
      { name := "Coverages", starred := true }] }

private def numberSource? : Option (CheckedNumberEntitySource model) :=
  (elaborateNumberEntitySource model ["Policy"] {
    first := .star starPath
    rest := [] }).toOption

private def filledSource? : Option (CheckedStarFieldPath model) :=
  (elaborateFilledFieldStarValidationSource model ["Policy"] starPath).toOption

private def filledGroupSource? : Option (CheckedStarredGroupSource model) :=
  (elaborateStarredGroupSource model ["Policy"] starredGroupPath).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr := [
  { group := 10, path := [1] },
  { group := 10, path := [2] },
  { group := 10, path := [3] }]

private def cell (row value : Nat) : ClassifiedCellInput :=
  { address := { field := premium.id, path := [row] }
    stored := toString value
    raw := .parsed (.num value) }

private def malformedCell (row : Nat) : ClassifiedCellInput :=
  { address := { field := premium.id, path := [row] }
    stored := "bad"
    raw := .rejected .malformed }

private def documentWith? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells }).toOption

private def aggregateWith? (op : NumericAggregateOp)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← numberSource?
  let document ← documentWith? cells
  (source.evaluateCheckedDocumentValidationAggregate op document []).toOption

private def sumWith? (cells : List ClassifiedCellInput) : Option NumericOperand :=
  aggregateWith? .sum cells

private def valueCountWith? (expected : Rat)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← numberSource?
  let document ← documentWith? cells
  (source.evaluateCheckedDocumentValueCountValidation expected document []).toOption

private def filledCountWith?
    (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let source ← filledSource?
  let document ← documentWith? cells
  (source.evaluateFilledFieldCountValidation document []).toOption

private def filledGroupCount? : Option FilledGroupCount := do
  let source ← filledGroupSource?
  (source.numberOfFilledGroups {
    instantiatedRows := rows
    rawCells := fun _ => none } []).toOption

/- The over-limit third row must not poison the ordinary starred aggregate or enter its sum. -/
example :
    sumWith? [cell 1 10, cell 2 20, cell 3 99] =
        some (.value 30 .fixed) ∧
    filledCountWith? [cell 1 10, cell 2 20, cell 3 99] =
        some (.value 2) ∧
    filledGroupCount? = some (.value 2) := by
  native_decide

/- Operators outside the measured three-consumer slice retain the complete formal-cell view rather than inheriting Sum's capacity projection. -/
example :
    aggregateWith? .minimum [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) ∧
    aggregateWith? .maximum [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) ∧
    aggregateWith? .distinctCount [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) ∧
    valueCountWith? 99 [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) := by
  native_decide

/- Capacity projection is not a blanket formal-error filter: an in-cap malformed row still makes both measured consumers unavailable. -/
example :
    sumWith? [cell 1 10, malformedCell 2, cell 3 99] =
        some (.unknown .malformed) ∧
    filledCountWith? [cell 1 10, malformedCell 2, cell 3 99] =
        some .unknown := by
  native_decide

end A12Kernel
