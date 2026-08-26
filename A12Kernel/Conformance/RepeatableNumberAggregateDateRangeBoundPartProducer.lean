import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # DateRange endpoint-component rows before a root Number aggregate

The matrix composes the existing checked addressed endpoint-component evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateDateRangeBoundPartProducer

open A12Kernel

private def rangeField (id : FieldId) (name format : String) : FlatFieldDecl := {
  id
  groupPath := ["Order", "Lines"]
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator := "/" }
  repeatableScope := [10]
}

private def rowDates := rangeField 1 "RowDates" "yyyy-MM-dd"
private def rowMonths := rangeField 2 "RowMonths" "MM"

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 0) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := false } }
}

private def produced := number 3 "Produced" ["Order", "Lines"] [10]
private def total := number 4 "Total" ["Order"] []
private def scaledProduced :=
  number 5 "ScaledProduced" ["Order", "Lines"] [10] 1

private def model : FlatModel := {
  fields := [rowDates, rowMonths, produced, total, scaledProduced]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 4
  }]
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Order" }, { name := "Lines", starred := true }]
  field
}

private def soleStar (field : String) : SurfaceNumberEntitySource := {
  first := .star (star field)
  rest := []
}

private def cascadeFor? (bound : DateRangeBound) (part : DateNumericPart) :=
  (checkRepeatableDateRangeBoundPartStarListAggregateCascade model
    ["Order", "Lines"] produced.id (bare "RowDates") bound part
    ["Order"] total.id (soleStar "Produced") .sum).toOption

private def cascade? := cascadeFor? .start .month

private def dateRangeCell (row : Nat) (stored : String) :
    ClassifiedCellInput := {
  address := { field := rowDates.id, path := [row] }
  stored
  raw :=
    match rowDates.toDateRangeDeclarationPolicy? with
    | some policy =>
        (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
          policy stored).toOption.getD .empty
    | none => .empty
}

private def numberCell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
}

private def input? (secondRange : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      dateRangeCell 1 "2024-06-01/2024-07-31",
      numberCell produced.id [1] 99,
      numberCell produced.id [2] 88,
      numberCell total.id [] 77
    ] ++ secondRange.toList
  }).toOption

private structure Snapshot where
  rows : List NumericTargetOutcome
  aggregate : NumericTargetOutcome
  deriving Repr, DecidableEq

private def snapshotFor? (bound : DateRangeBound) (part : DateNumericPart)
    (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← cascadeFor? bound part
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure { rows := outcomes.rows.map (·.outcome), aggregate := outcomes.aggregate.outcome }

private def snapshot? := snapshotFor? .start .month

private def accepted (value : Int) : NumericTargetOutcome :=
  .accepted { unscaled := value, scale := 0 }

private def expectedAnalysis : RepeatableNumberAggregateCascadeAnalysis := {
  producer := .dateRangeBoundPart .start .month
  consumer := .plain
  operation := .sum
  repeatableScope := [10]
  fieldDependencies := [
    (produced.id, [rowDates.id]),
    (total.id, [produced.id])]
}

private def expectedFinishQuarterAnalysis : RepeatableNumberAggregateCascadeAnalysis := {
  expectedAnalysis with producer := .dateRangeBoundPart .finish .quarter
}

private def producerMetadataMatches
    (plan : CheckedRepeatableNumberAggregateCascade model) : Bool :=
  plan.row.targetField == produced.id &&
    plan.row.targetDeclaration.id == produced.id &&
    plan.row.declaringGroup == produced.groupPath &&
    plan.row.targetDeclaration.repeatableScope == produced.repeatableScope

/- Analyze retains endpoint/component identity, the typed DateRange source edge, and exact target placement. -/
example :
    cascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedAnalysis ∧
    cascade?.map producerMetadataMatches = some true := by
  native_decide

/- A distinct endpoint and component guard against constant selector ownership in checking, execution, and analysis. -/
example :
    (cascadeFor? .finish .quarter).map
        CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedFinishQuarterAnalysis ∧
    snapshotFor? .finish .quarter (input? (some
      (dateRangeCell 2 "2024-01-15/2024-03-15"))) = some {
        rows := [accepted 3, accepted 1]
        aggregate := accepted 4
      } := by
  native_decide

/- Selected start months replace stale row targets before aggregation; absence and invalid range retain the addressed semantics. -/
example :
    snapshot? (input? (some
      (dateRangeCell 2 "2024-01-15/2024-03-15"))) = some {
      rows := [accepted 6, accepted 1]
      aggregate := accepted 7
    } ∧
    snapshot? (input? none) = some {
      rows := [accepted 6, accepted 0]
      aggregate := accepted 6
    } ∧
    snapshot? (input? (some
      (dateRangeCell 2 "2024-03-15/2024-01-15"))) = some {
      rows := [accepted 6, .inheritedPoison .dateRangeInvalid]
      aggregate := .inheritedPoison .computedDependency
    } := by
  native_decide

/- Endpoint-component admission failures retain their producer tag before aggregate certification. -/
example :
    (match checkRepeatableDateRangeBoundPartStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "RowMonths") .start .year
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.dateRangeBoundPart
          (.componentNotExposed path .year)) => path == rowMonths.path
      | _ => false) = true ∧
    (match checkRepeatableDateRangeBoundPartStarListAggregateCascade model
        ["Order", "Lines"] scaledProduced.id (bare "RowDates")
        .start .month ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.dateRangeBoundPart (.scaleMismatch 1 0)) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateDateRangeBoundPartProducer
