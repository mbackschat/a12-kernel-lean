import A12Kernel.Elaboration.NumericAggregate.Entities

/-! # Checked Number group computation

Checked-document computation over a starred Number group reuses the same recursive, operand-bounded
extent as full validation, then projects each cached cell at computation phase. These cases
specialize the retained Kernel computation matrix while keeping fixed groups, partial validation,
and raw-document routes outside this capsule.
-/

namespace A12Kernel.Conformance.NumberEntityGroupComputation

open A12Kernel

private def numberField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel) : FlatFieldDecl :=
  { id
    groupPath := groups
    name
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := scope }

private def model : FlatModel :=
  { fields := [
      numberField 1 ["Invoice", "Lines"] "Amount" [10],
      numberField 2 ["Invoice", "Charges"] "Fee" [20],
      numberField 3 ["Invoice", "Charges"] "Tax" [20],
      numberField 4 ["Invoice", "Charges", "Extras"] "Surcharge" [20, 30]]
    repeatableGroups := [
      { level := 10, path := ["Invoice", "Lines"], repeatability := some 10 },
      { level := 20, path := ["Invoice", "Charges"], repeatability := some 10 },
      { level := 30, path := ["Invoice", "Charges", "Extras"],
        repeatability := some 10 }] }

private def starredGroup (groups : List SurfaceStarGroupSegment) :
    SurfaceFieldEntityOperand :=
  .starredGroup { base := .absolute, groups }

private def source? (groups : List SurfaceStarGroupSegment) :
    Option (CheckedNumberEntitySource model) :=
  (elaborateNumberEntitySource model ["Invoice"] {
    first := starredGroup groups
    rest := [] }).toOption

private def linesSource? : Option (CheckedNumberEntitySource model) :=
  source? [{ name := "Invoice" }, { name := "Lines", starred := true }]

private def chargesSource? : Option (CheckedNumberEntitySource model) :=
  source? [{ name := "Invoice" }, { name := "Charges", starred := true }]

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def cell (field : FieldId) (path : List Nat)
    (value : Int) : ClassifiedCellInput :=
  { address := { field, path }
    stored := toString value
    raw := .parsed (.num value) }

private def malformedCell (field : FieldId) (path : List Nat) : ClassifiedCellInput :=
  { address := { field, path }
    stored := "bad"
    raw := .rejected .malformed }

private def aggregate? (source : Option (CheckedNumberEntitySource model))
    (op : NumericAggregateOp) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← source
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  (source.evaluateCheckedDocumentComputationAggregate op document []).toOption

private def valueCount? (source : Option (CheckedNumberEntitySource model))
    (expected : Rat) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← source
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  (source.evaluateCheckedDocumentValueCountComputation expected document []).toOption

private def lineRows : List RowAddr :=
  [{ group := 10, path := [1] },
    { group := 10, path := [2] },
    { group := 10, path := [3] }]

private def lineCells : List ClassifiedCellInput :=
  [cell 1 [1] 10, cell 1 [2] 20, cell 1 [3] 10]

/- The computation route preserves the common aggregate results over one starred group expansion. -/
example :
    aggregate? linesSource? .sum lineRows lineCells = some (.value 40 .fixed) ∧
      aggregate? linesSource? .minimum lineRows lineCells =
        some (.value 10 .fixed) ∧
      aggregate? linesSource? .maximum lineRows lineCells =
        some (.value 20 .fixed) ∧
      aggregate? linesSource? .distinctCount lineRows lineCells =
        some (.value 2 .fixed) := by
  native_decide

/- The shared computation resolver also makes the local Number value-count representation executable;
   Kernel correspondence for that literal admission and route remains unmeasured. -/
example :
    valueCount? linesSource? 10 lineRows lineCells = some (.value 2 .fixed) := by
  native_decide

private def chargeRows : List RowAddr :=
  [{ group := 20, path := [1] },
    { group := 20, path := [2] },
    { group := 30, path := [1, 1] },
    { group := 30, path := [1, 2] },
    { group := 30, path := [2, 1] }]

/- Recursive expansion reaches both direct declarations and every nested row, not one field or one
   nested coordinate. The empty `Tax` in row 2 remains the aggregate's internal growth direction. -/
example :
    aggregate? chargesSource? .sum chargeRows [
      cell 2 [1] 1,
      cell 3 [1] 2,
      cell 2 [2] 3,
      cell 4 [1, 1] 4,
      cell 4 [1, 2] 5,
      cell 4 [2, 1] 6] = some (.value 21 .growOnly) := by
  native_decide

/- The first formally unavailable reached cell poisons computation instead of being skipped. -/
example :
    aggregate? linesSource? .sum lineRows [
      cell 1 [1] 10,
      malformedCell 1 [2],
      cell 1 [3] 20] = some (.unknown .malformed) := by
  native_decide

/- An empty group computes the aggregate identity instead of refusing or manufacturing a row. -/
example :
    aggregate? linesSource? .sum [] [] = some (.value 0 .fixed) := by
  native_decide

end A12Kernel.Conformance.NumberEntityGroupComputation
