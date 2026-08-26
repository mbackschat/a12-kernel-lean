import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Field-exponent power rows before a root aggregate

The matrix composes the existing checked addressed power evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregatePowerProducer

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 0) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
}

private def outerExponent := number 1 "OuterExponent" ["Order"] []
private def base := number 2 "Base" ["Order", "Lines"] [10]
private def fractionalExponent :=
  number 3 "FractionalExponent" ["Order", "Lines"] [10] 1
private def produced := number 4 "Produced" ["Order", "Lines"] [10]
private def total := number 5 "Total" ["Order"] []

private def model : FlatModel := {
  fields := [outerExponent, base, fractionalExponent, produced, total]
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

private def cascade? (exponent : SurfaceFieldPath := root "OuterExponent") :=
  (checkRepeatableNumberPowerStarListAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Base") exponent true
    ["Order"] total.id (soleStar "Produced") .sum).toOption

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

private def input? (secondBase : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell outerExponent.id [] 2,
      cell base.id [1] 2,
      cell produced.id [1] 99,
      cell produced.id [2] 88,
      cell total.id [] 77
    ] ++ secondBase.toList
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
  producer := .power, consumer := .plain, operation := .sum
  repeatableScope := [10]
  fieldDependencies := [
    (produced.id, [base.id, outerExponent.id]),
    (total.id, [produced.id])]
}

private def producerMetadataMatches
    (plan : CheckedRepeatableNumberAggregateCascade model) : Bool :=
  plan.row.targetField == produced.id &&
    plan.row.targetDeclaration.id == produced.id &&
    plan.row.declaringGroup == produced.groupPath &&
    plan.row.targetDeclaration.repeatableScope == produced.repeatableScope

/- Analyze retains power identity, ordered sources, and exact target placement. -/
example :
    cascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedAnalysis ∧
    cascade?.map producerMetadataMatches = some true := by
  native_decide

/- Fresh powers replace stale row targets before aggregation; empty and poison keep the addressed power semantics. -/
example :
    snapshot? (input? (some (cell base.id [2] 3))) = some {
      rows := [accepted 4, accepted 9]
      aggregate := accepted 13
    } ∧
    snapshot? (input? none) = some {
      rows := [accepted 4, accepted 0]
      aggregate := accepted 4
    } ∧
    snapshot? (input? (some (malformed base.id [2]))) = some {
      rows := [accepted 4, .inheritedPoison .malformed]
      aggregate := .inheritedPoison .computedDependency
    } := by
  native_decide

/- Power-specific admission failures remain tagged, and the second source participates in the aggregate back-edge check. -/
example :
    (match checkRepeatableNumberPowerStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Base")
        (root "OuterExponent") false ["Order"] total.id
        (soleStar "Produced") .sum with
      | .error (.power .scaleSuppressionRequired) => true
      | _ => false) = true ∧
    (match checkRepeatableNumberPowerStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Base")
        (bare "FractionalExponent") true ["Order"] total.id
        (soleStar "Produced") .sum with
      | .error (.power (.invalidExponentScale 1)) => true
      | _ => false) = true ∧
    (match checkRepeatableNumberPowerStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Base") (root "Total") true
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.cycle field) => field == total.id
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregatePowerProducer
