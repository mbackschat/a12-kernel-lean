import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Warning-suppressed division rows before a root aggregate

The matrix composes the existing checked addressed division evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateDivisionProducer

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 2, signed := true } }
}

private def denominator := number 1 "Denominator" ["Order"] []
private def numerator := number 2 "Numerator" ["Order", "Lines"] [10]
private def produced := number 3 "Produced" ["Order", "Lines"] [10]
private def total := number 4 "Total" ["Order"] []

private def model : FlatModel := {
  fields := [denominator, numerator, produced, total]
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

private def cascade? :=
  (checkRepeatableNumberDivisionStarListAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Numerator")
    (root "Denominator") true ["Order"] total.id
    (soleStar "Produced") .sum).toOption

private def cell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
}

private def malformed (field : FieldId) (path : List Nat) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := "bad"
  raw := .rejected .malformed
}

private def input? (secondNumerator : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell denominator.id [] 4,
      cell numerator.id [1] 8,
      cell produced.id [1] 99,
      cell produced.id [2] 88,
      cell total.id [] 77
    ] ++ secondNumerator.toList
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

private def accepted (unscaled : Int) (scale : Nat) : NumericTargetOutcome :=
  .accepted { unscaled, scale }

private def expectedAnalysis : RepeatableNumberAggregateCascadeAnalysis := {
  producer := .division, consumer := .plain, operation := .sum
  repeatableScope := [10]
  fieldDependencies := [
    (produced.id, [numerator.id, denominator.id]),
    (total.id, [produced.id])]
}

private def producerMetadataMatches
    (plan : CheckedRepeatableNumberAggregateCascade model) : Bool :=
  plan.row.targetField == produced.id &&
    plan.row.targetDeclaration.id == produced.id &&
    plan.row.declaringGroup == produced.groupPath &&
    plan.row.targetDeclaration.repeatableScope == produced.repeatableScope

/- Analyze retains division identity, ordered sources, and exact target placement. -/
example :
    cascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedAnalysis ∧
    cascade?.map producerMetadataMatches = some true := by
  native_decide

/- Fresh quotients replace stale row targets before aggregation; empty and poison keep the addressed division semantics. -/
example :
    snapshot? (input? (some (cell numerator.id [2] 9))) = some {
      rows := [accepted 2 0, accepted 225 2]
      aggregate := accepted 425 2
    } ∧
    snapshot? (input? none) = some {
      rows := [accepted 2 0, accepted 0 0]
      aggregate := accepted 2 0
    } ∧
    snapshot? (input? (some (malformed numerator.id [2]))) = some {
      rows := [accepted 2 0, .inheritedPoison .malformed]
      aggregate := .inheritedPoison .computedDependency
    } := by
  native_decide

/- Division-specific admission failure remains tagged, and the second source participates in the aggregate back-edge check. -/
example :
    (match checkRepeatableNumberDivisionStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Numerator")
        (root "Denominator") false ["Order"] total.id
        (soleStar "Produced") .sum with
      | .error (.division .scaleSuppressionRequired) => true
      | _ => false) = true ∧
    (match checkRepeatableNumberDivisionStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Numerator") (root "Total") true
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.cycle field) => field == total.id
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateDivisionProducer
