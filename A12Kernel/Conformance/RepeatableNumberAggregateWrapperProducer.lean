import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Wrapped row producers before a root aggregate

The matrix keeps row-local `Abs` and Round transformations distinct from direct assignment while reusing the established rows-before-aggregate overlay.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateWrapperProducer

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
}

private def absSource := number 1 "AbsSource" ["Order", "Lines"] [10] 2
private def absProduced := number 2 "AbsProduced" ["Order", "Lines"] [10] 2
private def absTotal := number 3 "AbsTotal" ["Order"] [] 2
private def roundSource := number 4 "RoundSource" ["Order", "Lines"] [10] 2
private def roundProduced := number 5 "RoundProduced" ["Order", "Lines"] [10] 0
private def roundTotal := number 6 "RoundTotal" ["Order"] [] 0
private def outerAbsSource := number 7 "OuterAbsSource" ["Order"] [] 2
private def roundProduced1 := number 8 "RoundProduced1" ["Order", "Lines"] [10] 1
private def roundTotal1 := number 9 "RoundTotal1" ["Order"] [] 1
private def outerRoundSource := number 10 "OuterRoundSource" ["Order"] [] 2

private def model : FlatModel := {
  fields := [absSource, absProduced, absTotal, roundSource, roundProduced,
    roundTotal, outerAbsSource, roundProduced1, roundTotal1, outerRoundSource]
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

private def places0 : RoundingPlaces := ⟨0, by decide⟩
private def places1 : RoundingPlaces := ⟨1, by decide⟩

private def absCascadeFor? (source : SurfaceFieldPath) :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberAbsStarListAggregateCascade model
    ["Order", "Lines"] absProduced.id source
    ["Order"] absTotal.id (soleStar "AbsProduced") .sum).toOption

private def roundCascadeFor? (source : SurfaceFieldPath)
    (produced total : FlatFieldDecl) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberRoundStarListAggregateCascade model
    ["Order", "Lines"] produced.id source mode places
    ["Order"] total.id (soleStar produced.name) .sum).toOption

private def absCascade? := absCascadeFor? (bare "AbsSource")
private def outerAbsCascade? := absCascadeFor? (root "OuterAbsSource")

private def roundCascade? := roundCascadeFor? (bare "RoundSource")
  roundProduced roundTotal .floor places0
private def roundUpCascade? := roundCascadeFor? (bare "RoundSource")
  roundProduced roundTotal .ceiling places0
private def roundScaleOneCascade? := roundCascadeFor? (root "OuterRoundSource")
  roundProduced1 roundTotal1 .ceiling places1

private def decimalCell (field : FieldId) (path : List Nat) (stored : String)
    (unscaled scale : Int) (value : Rat) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.num value)
  numericDecimal := some { unscaled, scale }
}

private def malformed (field : FieldId) (path : List Nat) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := "bad"
  raw := .rejected .malformed
}

private def input? (secondAbs secondRound : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      decimalCell absSource.id [1] "-2.00" (-200) 2 (-2),
      decimalCell absProduced.id [1] "99.00" 9900 2 99,
      decimalCell absProduced.id [2] "88.00" 8800 2 88,
      decimalCell absTotal.id [] "77.00" 7700 2 77,
      decimalCell roundSource.id [1] "1.75" 175 2 (7 / 4),
      decimalCell roundProduced.id [1] "99" 99 0 99,
      decimalCell roundProduced.id [2] "88" 88 0 88,
      decimalCell roundTotal.id [] "77" 77 0 77
    ] ++ secondAbs.toList ++ secondRound.toList
  }).toOption

private def freshInput? : Option (CheckedDocument model) :=
  input? (some (decimalCell absSource.id [2] "3.50" 350 2 (7 / 2)))
    (some (decimalCell roundSource.id [2] "-1.25" (-125) 2 (-5 / 4)))

private structure Snapshot where
  rows : List NumericTargetOutcome
  aggregate : NumericTargetOutcome
  deriving Repr, DecidableEq

private def snapshot? (cascade : Option (CheckedRepeatableNumberAggregateCascade model))
    (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← cascade
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure {
    rows := outcomes.rows.map (·.outcome)
    aggregate := outcomes.aggregate.outcome
  }

private def accepted (unscaled : Int) (scale : Nat := 0) :
    NumericTargetOutcome :=
  .accepted { unscaled, scale }

private def expectedSnapshot (rows : List NumericTargetOutcome)
    (aggregate : NumericTargetOutcome) : Option Snapshot :=
  some { rows, aggregate }

private def expectedAnalysis (kind : RepeatableNumberAggregateProducerKind)
    (source produced total : FlatFieldDecl) :
    RepeatableNumberAggregateCascadeAnalysis := {
  producer := kind, consumer := .plain, operation := .sum
  repeatableScope := [10]
  fieldDependencies := [(produced.id, [source.id]), (total.id, [produced.id])]
}

private def producerMetadataMatches
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (source target : FlatFieldDecl) : Bool :=
  cascade.row.targetField == target.id && cascade.row.targetDeclaration.id == target.id &&
    cascade.row.declaringGroup == target.groupPath && cascade.row.targetDeclaration.repeatableScope == target.repeatableScope &&
    cascade.row.sourceFields == [source.id]

/- Both wrappers retain their own operation identity and source dependency before sharing the same aggregate stage. -/
example :
    absCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis .abs absSource absProduced absTotal) ∧
    roundCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis (.round .floor places0) roundSource
        roundProduced roundTotal) ∧
    roundUpCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis (.round .ceiling places0) roundSource
        roundProduced roundTotal) ∧
    outerAbsCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis .abs outerAbsSource absProduced absTotal) ∧
    roundScaleOneCascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some (expectedAnalysis (.round .ceiling places1) outerRoundSource
        roundProduced1 roundTotal1) := by
  native_decide

/- Asymmetric outer sources distinguish every wrapper target projection from its source projection. -/
example :
    outerAbsCascade?.map (producerMetadataMatches · outerAbsSource absProduced) =
      some true ∧
    roundScaleOneCascade?.map
      (producerMetadataMatches · outerRoundSource roundProduced1) = some true := by
  native_decide

/- The completed wrapper rows replace stale stored targets before aggregation. Empty and malformed rows retain the established zero and dependency-poison boundaries. -/
example :
    snapshot? absCascade? freshInput? =
      expectedSnapshot [accepted 2, accepted 35 1] (accepted 55 1) ∧
    snapshot? roundCascade? freshInput? =
      expectedSnapshot [accepted 1, accepted (-2)] (accepted (-1)) ∧
    snapshot? roundUpCascade? freshInput? =
      expectedSnapshot [accepted 2, accepted (-1)] (accepted 1) ∧
    snapshot? absCascade? (input? none
      (some (decimalCell roundSource.id [2] "-1.25" (-125) 2 (-5 / 4)))) =
      expectedSnapshot [accepted 2, accepted 0] (accepted 2) ∧
    snapshot? roundCascade? (input?
      (some (decimalCell absSource.id [2] "3.50" 350 2 (7 / 2)))
      (some (malformed roundSource.id [2]))) =
      expectedSnapshot [accepted 1, .inheritedPoison .malformed]
        (.inheritedPoison .computedDependency) := by
  native_decide

/- Wrapper-specific static failures remain visible, and either wrapper's source list still guards the aggregate back edge. -/
example :
    (match checkRepeatableNumberAbsStarListAggregateCascade model
        ["Order", "Lines"] roundProduced.id (bare "AbsSource")
        ["Order"] roundTotal.id (soleStar "RoundProduced") .sum with
      | .error (.abs (.scaleMismatch 0 2)) => true
      | _ => false) = true ∧
    (match checkRepeatableNumberRoundStarListAggregateCascade model
        ["Order", "Lines"] roundProduced.id (bare "RoundSource")
        .ceiling places1 ["Order"] roundTotal.id (soleStar "RoundProduced")
        .sum with
      | .error (.round (.scaleMismatch 0 1)) => true
      | _ => false) = true ∧
    (match checkRepeatableNumberAbsStarListAggregateCascade model
        ["Order", "Lines"] absProduced.id (root "AbsTotal")
        ["Order"] absTotal.id (soleStar "AbsProduced") .sum with
      | .error (.cycle field) => field == absTotal.id
      | _ => false) = true ∧
    (match checkRepeatableNumberRoundStarListAggregateCascade model
        ["Order", "Lines"] roundProduced.id (root "RoundTotal")
        .floor places0 ["Order"] roundTotal.id (soleStar "RoundProduced")
        .sum with
      | .error (.cycle field) => field == roundTotal.id
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateWrapperProducer
