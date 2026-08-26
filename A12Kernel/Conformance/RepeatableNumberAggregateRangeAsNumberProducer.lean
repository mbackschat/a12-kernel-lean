import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # String-range conversion rows before a root Number aggregate

The matrix composes the existing checked addressed `RangeAsNumber` evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateRangeAsNumberProducer

open A12Kernel

private def code : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Lines"]
  name := "Code"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 8 }
  repeatableScope := [10]
}

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 0) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := false } }
}

private def produced := number 2 "Produced" ["Order", "Lines"] [10]
private def total := number 3 "Total" ["Order"] []
private def wrong := number 4 "Wrong" ["Order", "Lines"] [10]
private def scaledProduced :=
  number 5 "ScaledProduced" ["Order", "Lines"] [10] 1

private def model : FlatModel := {
  fields := [code, produced, total, wrong, scaledProduced]
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

private def cascade? :=
  (checkRepeatableRangeAsNumberStarListAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Code") 4 5
    ["Order"] total.id (soleStar "Produced") .sum).toOption

private def stringCell (row : Nat) (stored : String) (raw : RawCell) :
    ClassifiedCellInput := {
  address := { field := code.id, path := [row] }
  stored
  raw
}

private def numberCell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
}

private def input? (secondCode : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      stringCell 1 "A😀12B" (.parsed (.str "A😀12B")),
      numberCell produced.id [1] 99,
      numberCell produced.id [2] 88,
      numberCell total.id [] 77
    ] ++ secondCode.toList
  }).toOption

private structure Snapshot where
  rows : List NumericTargetOutcome
  aggregate : NumericTargetOutcome
  deriving Repr, DecidableEq

private def snapshot? (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← cascade?
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure { rows := outcomes.rows.map (·.outcome), aggregate := outcomes.aggregate.outcome }

private def accepted (value : Int) : NumericTargetOutcome :=
  .accepted { unscaled := value, scale := 0 }

private def expectedAnalysis : RepeatableNumberAggregateCascadeAnalysis := {
  producer := .rangeAsNumber 4 5
  consumer := .plain
  operation := .sum
  repeatableScope := [10]
  fieldDependencies := [
    (produced.id, [code.id]),
    (total.id, [produced.id])]
}

private def producerMetadataMatches
    (plan : CheckedRepeatableNumberAggregateCascade model) : Bool :=
  plan.row.targetField == produced.id &&
    plan.row.targetDeclaration.id == produced.id &&
    plan.row.declaringGroup == produced.groupPath &&
    plan.row.targetDeclaration.repeatableScope == produced.repeatableScope

/- Analyze retains interval identity, the typed String source edge, and exact target placement. -/
example :
    cascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedAnalysis ∧
    cascade?.map producerMetadataMatches = some true := by
  native_decide

/- UTF-16 positions 4..5 select the two digits after one emoji and replace stale rows before aggregation. -/
example :
    snapshot? (input? (some
      (stringCell 2 "Z😀34Q" (.parsed (.str "Z😀34Q"))))) = some {
      rows := [accepted 12, accepted 34]
      aggregate := accepted 46
    } ∧
    snapshot? (input? none) = some {
      rows := [accepted 12, accepted 0]
      aggregate := accepted 12
    } ∧
    snapshot? (input? (some
      (stringCell 2 "bad" (.rejected .malformed)))) = some {
      rows := [accepted 12, .inheritedPoison .malformed]
      aggregate := .inheritedPoison .computedDependency
    } := by
  native_decide

/- Range-conversion admission failures retain their producer tag before aggregate certification. -/
example :
    (match checkRepeatableRangeAsNumberStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Code") 0 5
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.rangeAsNumber (.invalidRange 0 5)) => true
      | _ => false) = true ∧
    (match checkRepeatableRangeAsNumberStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Wrong") 4 5
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.rangeAsNumber (.sourceNotEvaluatedString path)) =>
          path == wrong.path
      | _ => false) = true ∧
    (match checkRepeatableRangeAsNumberStarListAggregateCascade model
        ["Order", "Lines"] scaledProduced.id (bare "Code") 4 5
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.rangeAsNumber (.scaleMismatch 1 0)) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateRangeAsNumberProducer
