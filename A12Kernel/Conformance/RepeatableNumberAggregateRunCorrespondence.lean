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
private def foreign := number 6 "Foreign" ["Order", "OtherLines"] [11]
private def unit := number 7 "Unit" ["Order", "Lines"] [10]

private def model : FlatModel := {
  fields := [candidate, produced, total, doubled, tripled, foreign, unit]
  repeatableGroups := [
    {
      level := 10
      path := ["Order", "Lines"]
      repeatability := some 5
    },
    {
      level := 11
      path := ["Order", "OtherLines"]
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

private def otherStar (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Order" },
    { name := "OtherLines", starred := true }]
  field
}

private def innerNumber (field : String) : SurfaceHavingNumberRef := {
  origin := .inner
  field := { base := .absolute, groups := ["Order", "Lines"], field }
}

private def otherInnerNumber (field : String) : SurfaceHavingNumberRef := {
  origin := .inner
  field := { base := .absolute, groups := ["Order", "OtherLines"], field }
}

private def candidateBelowProduced : SurfaceCorrelatedHaving :=
  .compareNumbers .less (innerNumber "Candidate") (innerNumber "Produced")

private def candidateBelowUnit : SurfaceCorrelatedHaving :=
  .compareNumbers .less (innerNumber "Candidate") (innerNumber "Unit")

private def foreignBelowItself : SurfaceCorrelatedHaving :=
  .compareNumbers .less (otherInnerNumber "Foreign")
    (otherInnerNumber "Foreign")

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

private def suffixRun? : Option (CheckedNumericComputationRun model) := do
  let doubledTable ← table? doubled.id total.id
    (.binary .add (rootNumber "Total") (rootNumber "Total"))
  let tripledTable ← table? tripled.id doubled.id
    (.binary .add (rootNumber "Doubled") (rootNumber "Total"))
  (certifyNumericComputationRun [doubledTable, tripledTable]).toOption

private def plan? : Option (CheckedRepeatableNumberAggregateRunCascade model) := do
  let cascade ← (checkRepeatableNumberAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate")
    ["Order"] total.id (star "Produced") .sum).toOption
  let run ← suffixRun?
  (checkRepeatableNumberAggregateRunCascade cascade run).toOption

private def multiPlan? :
    Option (CheckedRepeatableNumberAggregateRunCascade model) := do
  let cascade ← (checkRepeatableNumberMultiStarAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate")
    ["Order"] total.id (star "Candidate") (star "Produced") [] .sum).toOption
  let run ← suffixRun?
  (checkRepeatableNumberAggregateRunCascade cascade run).toOption

private def binaryMultiPlan? :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberBinaryMultiStarAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate") (bare "Unit") .add
    ["Order"] total.id (star "Candidate") (star "Produced") [] .sum).toOption

private def thirdOperandPlan? :
    Option (CheckedRepeatableNumberAggregateRunCascade model) := do
  let cascade ← (checkRepeatableNumberMultiStarAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate")
    ["Order"] total.id (star "Candidate") (star "Candidate")
      [star "Produced"] .sum).toOption
  let run ← suffixRun?
  (checkRepeatableNumberAggregateRunCascade cascade run).toOption

private def mixedCascade?
    (order : RepeatableNumberAggregateMixedOperandOrder) :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberMixedAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate")
    ["Order"] total.id (star "Candidate") (star "Produced")
    candidateBelowProduced order .sum).toOption

private def mixedPlan?
    (order : RepeatableNumberAggregateMixedOperandOrder) :
    Option (CheckedRepeatableNumberAggregateRunCascade model) := do
  let cascade ← mixedCascade? order
  let run ← suffixRun?
  (checkRepeatableNumberAggregateRunCascade cascade run).toOption

private def binaryMixedPlan? :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberBinaryMixedAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Candidate") (bare "Unit") .add
    ["Order"] total.id (star "Candidate") (star "Produced")
    candidateBelowProduced .plainThenFiltered .sum).toOption

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

private def snapshotFor?
    (plan : Option (CheckedRepeatableNumberAggregateRunCascade model))
    (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← plan
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure {
    rows := outcomes.cascade.rows.map (·.outcome)
    aggregate := outcomes.cascade.aggregate.outcome
    suffix := outcomes.scalars
  }

private def snapshot?
    (input : Option (CheckedDocument model)) : Option Snapshot :=
  snapshotFor? plan? input

private def multiSnapshot?
    (input : Option (CheckedDocument model)) : Option Snapshot :=
  snapshotFor? multiPlan? input

private def thirdOperandSnapshot?
    (input : Option (CheckedDocument model)) : Option Snapshot :=
  snapshotFor? thirdOperandPlan? input

private def mixedSnapshot?
    (order : RepeatableNumberAggregateMixedOperandOrder)
    (input : Option (CheckedDocument model)) : Option Snapshot :=
  snapshotFor? (mixedPlan? order) input

private def mixedMatrix?
    (order : RepeatableNumberAggregateMixedOperandOrder) :
    Option (List Snapshot) :=
  [
    inputWithRows? (some (cell candidate.id [2] (-3))),
    inputWithRows? none,
    inputWithRows? (some malformedCandidate),
    noRowsInput?
  ].mapM (mixedSnapshot? order)

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

/- Each filtered wildcard owns only its own filter, while both authored orders read the completed producer overlay. The two Analyze views retain their different first-occurrence dependency order. -/
example :
    (mixedCascade? .plainThenFiltered).map
        CheckedRepeatableNumberAggregateCascade.analyze =
      some {
        producer := .direct
        consumer := .mixed
        operation := .sum
        repeatableScope := [10]
        fieldDependencies := [
          (produced.id, [candidate.id]),
          (total.id, [candidate.id, produced.id])]
      } ∧
    (mixedCascade? .filteredThenPlain).map
        CheckedRepeatableNumberAggregateCascade.analyze =
      some {
        producer := .direct
        consumer := .mixed
        operation := .sum
        repeatableScope := [10]
        fieldDependencies := [
          (produced.id, [candidate.id]),
          (total.id, [produced.id, candidate.id])]
      } ∧
    binaryMixedPlan?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some {
        producer := .binary .add
        consumer := .mixed
        operation := .sum
        repeatableScope := [10]
        fieldDependencies := [
          (produced.id, [candidate.id, unit.id]),
          (total.id, [candidate.id, produced.id])]
      } := by
  native_decide

/- The retained Kernel matrix separates completed filter state from stale stored `Produced` values, empty substitution, reached malformed poison, and the no-row identity. -/
example :
    let expected : List Snapshot := [
      {
        rows := [accepted 2, accepted (-3)]
        aggregate := accepted (-1)
        suffix := [(doubled.id, accepted (-2)), (tripled.id, accepted (-3))]
      },
      {
        rows := [accepted 2, accepted 0]
        aggregate := accepted 2
        suffix := [(doubled.id, accepted 4), (tripled.id, accepted 6)]
      },
      {
        rows := [accepted 2, .inheritedPoison .malformed]
        aggregate := .inheritedPoison .malformed
        suffix := [
          (doubled.id, .inheritedPoison .computedDependency),
          (tripled.id, .inheritedPoison .computedDependency)]
      },
      {
        rows := []
        aggregate := accepted 0
        suffix := [(doubled.id, accepted 0), (tripled.id, accepted 0)]
      }]
    mixedMatrix? .plainThenFiltered = some expected ∧
      mixedMatrix? .filteredThenPlain = some expected := by
  native_decide

/- A mixed consumer must read its producer either as the plain value or inside the filtered slot's `Having`. Merely aggregating the producer in that slot does not form a dependency, and every value source still belongs to the producer's exact group. -/
example :
    (match checkRepeatableNumberMixedAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Candidate")
        ["Order"] total.id (star "Candidate") (star "Candidate")
        candidateBelowUnit .plainThenFiltered .sum with
      | .error (.missingMixedDependency field) => field == produced.id
      | _ => false) = true ∧
    (match checkRepeatableNumberMixedAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Candidate")
        ["Order"] total.id (star "Candidate") (star "Produced")
        candidateBelowUnit .filteredThenPlain .sum with
      | .error (.missingMixedDependency field) => field == produced.id
      | _ => false) = true ∧
    (match checkRepeatableNumberMixedAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Candidate")
        ["Order"] total.id (star "Produced") (otherStar "Foreign")
        foreignBelowItself .plainThenFiltered .sum with
      | .error (.groupMismatch producerGroup aggregateGroup) =>
          producerGroup == ["Order", "Lines"] &&
            aggregateGroup == ["Order", "OtherLines"]
      | _ => false) = true := by
  native_decide

/- A later aggregate operand may read the completed producer without moving it
ahead of the earlier direct operand in Analyze or execution. -/
example :
    binaryMultiPlan?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some {
        producer := .binary .add
        consumer := .plain
        operation := .sum
        repeatableScope := [10]
        fieldDependencies := [
          (produced.id, [candidate.id, unit.id]),
          (total.id, [candidate.id, produced.id])]
      } ∧
    multiPlan?.map (fun plan => plan.cascade.analyze.fieldDependencies) =
      some [
        (produced.id, [candidate.id]),
        (total.id, [candidate.id, produced.id])] ∧
    multiSnapshot? (inputWithRows? (some (cell candidate.id [2] 3))) = some {
      rows := [accepted 2, accepted 3]
      aggregate := accepted 10
      suffix := [(doubled.id, accepted 20), (tripled.id, accepted 30)]
    } ∧
    multiSnapshot? (inputWithRows? none) = some {
      rows := [accepted 2, accepted 0]
      aggregate := accepted 4
      suffix := [(doubled.id, accepted 8), (tripled.id, accepted 12)]
    } ∧
    multiSnapshot? (inputWithRows? (some malformedCandidate)) = some {
      rows := [
        accepted 2,
        .inheritedPoison .malformed]
      aggregate := .inheritedPoison .malformed
      suffix := [
        (doubled.id, .inheritedPoison .computedDependency),
        (tripled.id, .inheritedPoison .computedDependency)]
    } ∧
    multiSnapshot? noRowsInput? = some {
      rows := []
      aggregate := accepted 0
      suffix := [(doubled.id, accepted 0), (tripled.id, accepted 0)]
    } ∧
    thirdOperandPlan?.map (fun plan =>
        plan.cascade.analyze.fieldDependencies) =
      some [
        (produced.id, [candidate.id]),
        (total.id, [candidate.id, produced.id])] ∧
    thirdOperandSnapshot?
        (inputWithRows? (some (cell candidate.id [2] 3))) = some {
      rows := [accepted 2, accepted 3]
      aggregate := accepted 15
      suffix := [(doubled.id, accepted 30), (tripled.id, accepted 45)]
    } := by
  native_decide

/- Every plain starred operand belongs to the producer's exact group, not just
the operand that happens to carry the stage-forming dependency. -/
example :
    (match checkRepeatableNumberMultiStarAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Candidate")
        ["Order"] total.id (star "Candidate") (star "Candidate") [] .sum with
      | .error (.dependency expected actual) =>
          expected == produced.id && actual == candidate.id
      | _ => false) = true ∧
    (match checkRepeatableNumberMultiStarAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Candidate")
        ["Order"] total.id (star "Produced") (otherStar "Foreign") [] .sum with
      | .error (.groupMismatch producerGroup aggregateGroup) =>
          producerGroup == ["Order", "Lines"] &&
            aggregateGroup == ["Order", "OtherLines"]
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateRunCorrespondence
