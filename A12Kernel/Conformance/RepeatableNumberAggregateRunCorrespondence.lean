import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Aggregate-seeded finite Number correspondence lock -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateRunCorrespondence

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }
}

private def candidate := number 1 "Candidate" ["Order", "Lines"] [10]
private def produced := number 2 "Produced" ["Order", "Lines"] [10]
private def total := number 3 "Total" ["Order"] []
private def doubled := number 4 "Doubled" ["Order"] []
private def tripled := number 5 "Tripled" ["Order"] []

private def model : FlatModel := {
  fields := [candidate, produced, total, doubled, tripled]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 5
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
  groups := [
    { name := "Order" },
    { name := "Lines", starred := true }]
  field
}

private def rootNumber (field : String) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.field (bare field)))

private def table? (target guard : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateCompleteNumericTargetComputationOperation
    model ["Order"] target expression).toOption
  (certifyNumericComputationTable [{
    precondition := .fieldFilled guard
    operation
  }]).toOption

private def plan? : Option (CheckedRepeatableNumberAggregateRunCascade model) := do
  let cascade ← (checkRepeatableNumberAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate")
    ["Order"] total.id (star "Produced") .sum).toOption
  let doubledTable ← table? doubled.id total.id
    (.binary .add (rootNumber "Total") (rootNumber "Total"))
  let tripledTable ← table? tripled.id doubled.id
    (.binary .add (rootNumber "Doubled") (rootNumber "Total"))
  let run ← (certifyNumericComputationRun
    [doubledTable, tripledTable]).toOption
  (checkRepeatableNumberAggregateRunCascade cascade run).toOption

private def cell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def malformedCandidate : ClassifiedCellInput := {
  address := { field := candidate.id, path := [2] }
  stored := "bad"
  raw := .rejected .malformed
}

private def inputWithRows?
    (secondCandidate : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell candidate.id [1] 2,
      cell produced.id [1] 4,
      cell produced.id [2] 6,
      cell total.id [] 9,
      cell doubled.id [] 7,
      cell tripled.id [] 5
    ] ++ secondCandidate.toList
  }).toOption

private def noRowsInput? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      cell total.id [] 9,
      cell doubled.id [] 7,
      cell tripled.id [] 5]
  }).toOption

private structure Snapshot where
  rows : List NumericTargetOutcome
  aggregate : NumericTargetOutcome
  suffix : List (FieldId × NumericTargetOutcome)
  deriving Repr, DecidableEq

private def snapshot?
    (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← plan?
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure {
    rows := outcomes.cascade.rows.map (·.outcome)
    aggregate := outcomes.cascade.aggregate.outcome
    suffix := outcomes.scalars
  }

private def accepted (value : Int) : NumericTargetOutcome :=
  .accepted { unscaled := value, scale := 0 }

/- The retained Kernel matrix separates fresh state, empty substitution,
reached dependency poison, and the no-row aggregate identity. -/
example :
    snapshot? (inputWithRows? (some (cell candidate.id [2] 3))) = some {
      rows := [accepted 2, accepted 3]
      aggregate := accepted 5
      suffix := [(doubled.id, accepted 10), (tripled.id, accepted 15)]
    } ∧
    snapshot? (inputWithRows? none) = some {
      rows := [accepted 2, accepted 0]
      aggregate := accepted 2
      suffix := [(doubled.id, accepted 4), (tripled.id, accepted 6)]
    } ∧
    snapshot? (inputWithRows? (some malformedCandidate)) = some {
      rows := [
        accepted 2,
        .inheritedPoison .malformed]
      aggregate := .inheritedPoison .computedDependency
      suffix := [
        (doubled.id, .inheritedPoison .computedDependency),
        (tripled.id, .inheritedPoison .computedDependency)]
    } ∧
    snapshot? noRowsInput? = some {
      rows := []
      aggregate := accepted 0
      suffix := [(doubled.id, accepted 0), (tripled.id, accepted 0)]
    } := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateRunCorrespondence
