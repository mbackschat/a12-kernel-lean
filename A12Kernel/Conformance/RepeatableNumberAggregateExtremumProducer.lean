import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Operand-list extremum rows before a root aggregate

The matrix composes the existing ordered addressed `Min`/`Max` evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateExtremumProducer

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 0) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
}

private def outer := number 1 "Outer" ["Order"] []
private def a := number 2 "A" ["Order", "Lines"] [10]
private def b := number 3 "B" ["Order", "Lines"] [10]
private def producedMin := number 4 "ProducedMin" ["Order", "Lines"] [10]
private def producedMax := number 5 "ProducedMax" ["Order", "Lines"] [10]
private def minTotal := number 6 "MinTotal" ["Order"] []
private def maxTotal := number 7 "MaxTotal" ["Order"] []
private def scaleOne := number 8 "ScaleOne" ["Order", "Lines"] [10] 1

private def model : FlatModel := {
  fields := [outer, a, b, producedMin, producedMax, minTotal, maxTotal, scaleOne]
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

private def root (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Order" }, { name := "Lines", starred := true }]
  field
}

private def soleStar (field : String) : SurfaceNumberEntitySource := {
  first := .star (star field)
  rest := []
}

private def rowField (name : String) : SurfaceAddressedNumberExtremumOperand :=
  .field (bare name)

private def rootField (name : String) : SurfaceAddressedNumberExtremumOperand :=
  .field (root name)

private def cascade? (target total : FlatFieldDecl) (op : NumericExtremumOp)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :=
  (checkRepeatableNumberExtremumStarListAggregateCascade model
    ["Order", "Lines"] target.id first rest op
    ["Order"] total.id (soleStar target.name) .sum).toOption

private def minCascade? := cascade? producedMin minTotal .minimum
  (rootField "Outer") [rowField "A", rowField "A", rowField "B"]

private def maxCascade? := cascade? producedMax maxTotal .maximum
  (rowField "B") [rootField "Outer", rowField "A"]

private def cell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def malformed (field : FieldId) (path : List Nat) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := "bad"
  raw := .rejected .malformed
}

private def input? (secondA secondB : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell outer.id [] 4,
      cell a.id [1] 2,
      cell b.id [1] 6,
      cell producedMin.id [1] 99,
      cell producedMin.id [2] 88,
      cell producedMax.id [1] 77,
      cell producedMax.id [2] 66,
      cell minTotal.id [] 55,
      cell maxTotal.id [] 44
    ] ++ secondA.toList ++ secondB.toList
  }).toOption

private structure Snapshot where
  rows : List NumericTargetOutcome
  aggregate : NumericTargetOutcome
  deriving Repr, DecidableEq

private def snapshot? (cascade : Option (CheckedRepeatableNumberAggregateCascade model))
    (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← cascade
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure { rows := outcomes.rows.map (·.outcome), aggregate := outcomes.aggregate.outcome }

private def accepted (value : Int) : NumericTargetOutcome :=
  .accepted { unscaled := value, scale := 0 }

private def expectedAnalysis (kind : RepeatableNumberAggregateProducerKind)
    (sources : List FieldId) (target total : FlatFieldDecl) :
    RepeatableNumberAggregateCascadeAnalysis := {
  producer := kind, consumer := .plain, operation := .sum
  repeatableScope := [10]
  fieldDependencies := [(target.id, sources), (total.id, [target.id])]
}

private def producerMetadataMatches
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (target : FlatFieldDecl) : Bool :=
  cascade.row.targetField == target.id && cascade.row.targetDeclaration.id == target.id &&
    cascade.row.declaringGroup == target.groupPath &&
    cascade.row.targetDeclaration.repeatableScope == target.repeatableScope

/- Min and Max retain their selector and exact authored dependency order. -/
example :
    minCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis (.extremum .minimum) [outer.id, a.id, a.id, b.id]
        producedMin minTotal) ∧
    maxCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis (.extremum .maximum) [b.id, outer.id, a.id]
        producedMax maxTotal) ∧
    minCascade?.map (producerMetadataMatches · producedMin) = some true ∧
    maxCascade?.map (producerMetadataMatches · producedMax) = some true := by
  native_decide

/- Fresh extrema replace stale row targets before aggregation; empty and poison retain their established row-local meanings. -/
example :
    snapshot? minCascade? (input? (some (cell a.id [2] 3))
      (some (cell b.id [2] 5))) = some {
        rows := [accepted 2, accepted 3]
        aggregate := accepted 5
      } ∧
    snapshot? maxCascade? (input? (some (cell a.id [2] 7))
      (some (cell b.id [2] 5))) = some {
        rows := [accepted 6, accepted 7]
        aggregate := accepted 13
      } ∧
    snapshot? minCascade? (input? none (some (cell b.id [2] 5))) = some {
        rows := [accepted 2, accepted 0]
        aggregate := accepted 2
      } ∧
    snapshot? minCascade? (input? (some (cell a.id [2] 3))
      (some (malformed b.id [2]))) = some {
        rows := [accepted 2, .inheritedPoison .malformed]
        aggregate := .inheritedPoison .computedDependency
      } := by
  native_decide

/- Extremum-specific admission errors remain tagged, and every ordered source participates in the back-edge check. -/
example :
    (match checkRepeatableNumberExtremumStarListAggregateCascade model
        ["Order", "Lines"] producedMin.id (rowField "ScaleOne") [] .minimum
        ["Order"] minTotal.id (soleStar "ProducedMin") .sum with
      | .error (.extremum (.scaleMismatch 0 summary)) =>
          summary.scale == ScaleInfo.exact 1
      | _ => false) = true ∧
    (match checkRepeatableNumberExtremumStarListAggregateCascade model
        ["Order", "Lines"] producedMin.id (rowField "A")
        [rootField "MinTotal"] .minimum ["Order"] minTotal.id
        (soleStar "ProducedMin") .sum with
      | .error (.cycle field) => field == minTotal.id
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateExtremumProducer
