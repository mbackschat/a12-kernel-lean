import A12Kernel.Elaboration.NumericComputation.LaterValidation

/-! # One-level Number application then validation locks -/

namespace A12Kernel.Conformance.NumericComputation.LaterValidation

open A12Kernel

private def amount : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Lines"]
  name := "Amount"
  repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := true } }
}

private def model : FlatModel := {
  fields := [amount]
  baseYear := some 2020
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 3
  }]
}

private def path : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order", "Lines"]
  field := "Amount"
}

private def positiveComparison? :
    Option (CheckedOrderedNumericComparison model) :=
  (elaborateRepeatableNumericComparison model ["Order", "Lines"] {
    op := .ordinary .greater
    left := .atom (.field path)
    right := .literal { value := 0, authoredScale := 0 }
  }).toOption

private def checked? (rows : List Nat := [])
    (values : List (Nat × Int) := []) : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
  let source : DocumentData := {
    instantiatedRows := rows.map fun coordinate =>
      { group := 10, path := [coordinate] }
    cells := values.map fun entry => {
      address := { field := amount.id, path := [entry.1] }
      stored := toString entry.2
      raw := .parsed (.num entry.2)
      numericDecimal := some { unscaled := entry.2, scale := 0 }
    }
  }
  (checkDocument prepared "en_US" source).toOption

private def accepted (coordinate : Nat) (value : Int) :
    SourcedNumericTargetOutcome CellAddr := {
  targetField := { field := amount.id, path := [coordinate] }
  outcome := .accepted { unscaled := value, scale := 0 }
  source := .absent
}

private def rejected (coordinate : Nat) (attempted source : Int) :
    SourcedNumericTargetOutcome CellAddr := {
  targetField := { field := amount.id, path := [coordinate] }
  outcome := .rejected { unscaled := attempted, scale := 0 } .aboveMaximum
  source := .presentValue
    (.decimal { unscaled := source, scale := 0 })
}

private def cleared (coordinate : Nat) (source : Int) :
    SourcedNumericTargetOutcome CellAddr := {
  targetField := { field := amount.id, path := [coordinate] }
  outcome := .noValue
  source := .presentValue
    (.decimal { unscaled := source, scale := 0 })
}

private def appliedView (outcomes : List (SourcedNumericTargetOutcome CellAddr)) :
    NumericComputationRunView Bool CellAddr :=
  NumericComputationRunView.fromPartitionedSourceOutcomes [] outcomes

private def evaluate? (destination : CheckedDocument model)
    (outcomes : List (SourcedNumericTargetOutcome CellAddr)) :
    Option (List (Env × Verdict)) := do
  let comparison ← positiveComparison?
  ((appliedView outcomes).evaluateOneLevelAfterApplication
    destination 10 comparison).toOption

private def emptyDestinationResult? : Option (List (Env × Verdict)) := do
  let destination ← checked?
  evaluate? destination [accepted 1 5, accepted 3 7]

/- Later validation runs over the normalized applied prefix, so applied values fire at their exact rows while the materialized empty predecessor does not. -/
example : emptyDestinationResult? = some [
    ([(10, 1)], .fired .value),
    ([(10, 2)], .notFired),
    ([(10, 3)], .fired .value)
  ] := by
  native_decide

private def preservingDestinationResult? : Option (List (Env × Verdict)) := do
  let destination ← checked? [1, 2] [(2, 4)]
  evaluate? destination [accepted 3 7]

/- The validation phase reads the applied destination, including an unrelated pre-existing positive value; it cannot be reconstructed from computation outcomes alone. -/
example : preservingDestinationResult? = some [
    ([(10, 1)], .notFired),
    ([(10, 2)], .fired .value),
    ([(10, 3)], .fired .value)
  ] := by
  native_decide

private def rejectedDestinationResult? : Option (List (Env × Verdict)) := do
  let destination ← checked? [1, 2] [(2, 4)]
  evaluate? destination [rejected 2 8 4, accepted 3 7]

/- A retained target error clears the existing positive destination target before validation; the attempted rejected value is not validation input. -/
example : rejectedDestinationResult? = some [
    ([(10, 1)], .notFired),
    ([(10, 2)], .notFired),
    ([(10, 3)], .fired .value)
  ] := by
  native_decide

private def clearedDestinationResult? : Option (List (Env × Verdict)) := do
  let destination ← checked? [1, 2] [(2, 4)]
  evaluate? destination [cleared 2 4, accepted 3 7]

/- A source-classified retained clear replaces the existing positive destination value before validation, independently of the target-error route. -/
example : clearedDestinationResult? = some [
    ([(10, 1)], .notFired),
    ([(10, 2)], .notFired),
    ([(10, 3)], .fired .value)
  ] := by
  native_decide

private def baseYearComparison? :
    Option (CheckedOrderedNumericComparison model) :=
  (elaborateRepeatableNumericComparison model ["Order", "Lines"] {
    op := .ordinary .greater
    left := .atom (.baseYear)
    right := .atom (.field path)
  }).toOption

private def unsupportedRefused : Bool :=
  match (do
    let destination ← checked?
    let comparison ← baseYearComparison?
    pure ((appliedView [accepted 1 5]).evaluateOneLevelAfterApplication
      destination 10 comparison)) with
  | some (.error .unsupportedComparison) => true
  | _ => false

/- This composition refuses even an otherwise checked Base-Year atom rather than widening itself into a generic addressed validation runner. -/
example : unsupportedRefused = true := by
  native_decide

end A12Kernel.Conformance.NumericComputation.LaterValidation
