import A12Kernel.Elaboration.NumericComputation.LaterValidation

/-! # Finite two-level Number result application locks -/

namespace A12Kernel.Conformance.NumericComputation.NestedApplication

open A12Kernel

private def nestedNumber (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Order", "Outer", "Inner"]
  repeatableScope := [10, 20]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def amount := nestedNumber 1 "Amount"
private def candidate := nestedNumber 2 "Candidate"
private def outerAmount : FlatFieldDecl := {
  amount with
  id := 3
  name := "OuterAmount"
  groupPath := ["Order", "Outer"]
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [amount, candidate, outerAmount]
  repeatableGroups := [{
    level := 10, path := ["Order", "Outer"], repeatability := some 3
  }, {
    level := 20, path := ["Order", "Outer", "Inner"], repeatability := some 4
  }]
}

private def checked? (source : DocumentData) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" source).toOption

private def outerRow (outer : Nat) : RowAddr := { group := 10, path := [outer] }
private def innerRow (outer inner : Nat) : RowAddr := { group := 20, path := [outer, inner] }
private def address (field : FieldId) (outer inner : Nat) : CellAddr :=
  { field, path := [outer, inner] }

private def empty? : Option (CheckedDocument model) := checked? {
  instantiatedRows := []
  cells := []
}

private def preserving? : Option (CheckedDocument model) := checked? {
  instantiatedRows := [outerRow 1, outerRow 2, outerRow 3, innerRow 3 1, innerRow 3 2]
  cells := [{
    address := address candidate.id 3 2
    stored := "4", raw := .parsed (.num 4)
    numericDecimal := some { unscaled := 4, scale := 0 }
  }]
}

private def cleared (outer inner : Nat) : SourcedNumericTargetOutcome CellAddr := {
  targetField := address amount.id outer inner
  outcome := .noValue
  source := .presentValue (.decimal { unscaled := 9, scale := 0 })
}

private def value (outer inner value : Nat) : SourcedNumericTargetOutcome CellAddr := {
  targetField := address amount.id outer inner
  outcome := .accepted { unscaled := Int.ofNat value, scale := 0 }
  source := .absent
}

private def errored (outer inner : Nat) : SourcedNumericTargetOutcome CellAddr := {
  targetField := address amount.id outer inner
  outcome := .rejected { unscaled := 8, scale := 0 } .aboveMaximum
  source := .presentValue (.decimal { unscaled := 9, scale := 0 })
}

private def view (entries : List (SourcedNumericTargetOutcome CellAddr)) :
    NumericComputationRunView Bool CellAddr :=
  NumericComputationRunView.fromPartitionedSourceOutcomes [] entries

private def expectedLeaves :=
  [innerRow 1 1, innerRow 1 2,
    innerRow 3 1, innerRow 3 2, innerRow 3 3, innerRow 3 4]

private def topologyMatrixHolds : Bool := (do
  let empty ← empty?
  let preserving ← preserving?
  let reverse ← (view [cleared 1 2, value 3 4 7])
    |>.applyToCheckedTwoLevel empty 10 20 |>.toOption
  let forward ← (view [cleared 3 4, value 1 2 7])
    |>.applyToCheckedTwoLevel empty 10 20 |>.toOption
  let preserved ← (view [cleared 1 2, value 3 4 7])
    |>.applyToCheckedTwoLevel preserving 10 20 |>.toOption
  let rejected ← (view [errored 3 4])
    |>.applyToCheckedTwoLevel empty 10 20 |>.toOption
  pure (
    reverse.outerRows == [outerRow 1, outerRow 2, outerRow 3] &&
    reverse.innerRowsAt 1 == [innerRow 1 1, innerRow 1 2] &&
    reverse.innerRowsAt 2 == [] && reverse.innerRowsAt 3 == expectedLeaves.drop 2 &&
    reverse.leafRows == expectedLeaves &&
    reverse.stateAt (address amount.id 1 2) == NumericTargetState.presentEmpty &&
    reverse.stateAt (address amount.id 3 4) ==
      NumericTargetState.presentValue (.decimal { unscaled := 7, scale := 0 }) &&
    forward.leafRows == expectedLeaves &&
    forward.stateAt (address amount.id 1 2) ==
      NumericTargetState.presentValue (.decimal { unscaled := 7, scale := 0 }) &&
    forward.stateAt (address amount.id 3 4) == NumericTargetState.presentEmpty &&
    preserved.innerRowsAt 1 == [innerRow 1 1, innerRow 1 2] &&
    preserved.innerRowsAt 2 == [] &&
    preserved.innerRowsAt 3 == [innerRow 3 1, innerRow 3 2,
      innerRow 3 3, innerRow 3 4] &&
    preserved.stateAt (address candidate.id 3 2) ==
      NumericTargetState.presentValue (.decimal { unscaled := 4, scale := 0 }) &&
    rejected.outerRows == [] && rejected.leafRows == [] &&
    rejected.stateAt (address amount.id 3 4) == NumericTargetState.absent)
  ).getD false

/- Two-level application pads predecessors only in the addressed parent, keeps action coordinates, preserves destination cells, and does not materialize an absent ERRORED target. -/
example : topologyMatrixHolds = true := by native_decide

private def amountPath : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order", "Outer", "Inner"]
  field := "Amount"
}

private def positiveComparison? :
    Option (CheckedOrderedNumericComparison model) :=
  (elaborateRepeatableNumericComparison model
    ["Order", "Outer", "Inner"] {
      op := .ordinary .greater
      left := .atom (.field amountPath)
      right := .literal { value := 0, authoredScale := 0 }
    }).toOption

private def laterValidation? : Option (List (Env × Verdict)) := do
  let destination ← empty?
  let comparison ← positiveComparison?
  ((view [value 1 2 5, value 3 4 7])
    |>.evaluateTwoLevelAfterApplication
      destination 10 20 comparison).toOption

/- Later validation uses the checked addressed evaluator over parent-scoped inner prefixes. Synthetic outer predecessors without an inner row do not become validation rows. -/
example : laterValidation? = some [
    ([(10, 1), (20, 1)], .notFired),
    ([(10, 1), (20, 2)], .fired .value),
    ([(10, 3), (20, 1)], .notFired),
    ([(10, 3), (20, 2)], .notFired),
    ([(10, 3), (20, 3)], .notFired),
    ([(10, 3), (20, 4)], .fired .value)
  ] := by
  native_decide

private def laterDestination? : Option (CheckedDocument model) := checked? {
  instantiatedRows := [
    outerRow 1, outerRow 2, outerRow 3,
    innerRow 1 1, innerRow 1 2, innerRow 3 1, innerRow 3 2]
  cells := [{
    address := address amount.id 3 2
    stored := "4", raw := .parsed (.num 4)
    numericDecimal := some { unscaled := 4, scale := 0 }
  }]
}

private def laterValidationWith?
    (entries : List (SourcedNumericTargetOutcome CellAddr)) :
    Option (List (Env × Verdict)) := do
  let destination ← laterDestination?
  let comparison ← positiveComparison?
  ((view entries).evaluateTwoLevelAfterApplication
    destination 10 20 comparison).toOption

private def nestedPreservingVerdicts := [
  ([(10, 1), (20, 1)], Verdict.notFired),
  ([(10, 1), (20, 2)], Verdict.notFired),
  ([(10, 3), (20, 1)], Verdict.notFired),
  ([(10, 3), (20, 2)], Verdict.fired .value),
  ([(10, 3), (20, 3)], Verdict.notFired),
  ([(10, 3), (20, 4)], Verdict.fired .value)
]

/- Later validation reads a pre-existing destination value below its exact parent while also observing the applied extension. -/
example : laterValidationWith? [value 3 4 7] =
    some nestedPreservingVerdicts := by
  native_decide

private def nestedClearedVerdicts := [
  ([(10, 1), (20, 1)], Verdict.notFired),
  ([(10, 1), (20, 2)], Verdict.notFired),
  ([(10, 3), (20, 1)], Verdict.notFired),
  ([(10, 3), (20, 2)], Verdict.notFired),
  ([(10, 3), (20, 3)], Verdict.notFired),
  ([(10, 3), (20, 4)], Verdict.fired .value)
]

/- Target rejection and retained clear both remove the pre-existing destination value before validation; the applied sibling still fires. -/
example :
    laterValidationWith? [errored 3 2, value 3 4 7] =
        some nestedClearedVerdicts ∧
      laterValidationWith? [cleared 3 2, value 3 4 7] =
        some nestedClearedVerdicts := by
  native_decide

private def applicationError? (entry : SourcedNumericTargetOutcome CellAddr) :
    Option NumericComputationDocumentApplicationError := do
  let destination ← empty?
  match (view [entry]).applyToCheckedTwoLevel destination 10 20 with
  | .error error => some error
  | .ok _ => none

private def topologyError? (outer inner : RepeatableLevel) :
    Option NumericComputationDocumentApplicationError := do
  let destination ← empty?
  match (view []).applyToCheckedTwoLevel destination outer inner with
  | .error error => some error
  | .ok _ => none

/- The bounded route refuses both over-capacity coordinates, a target outside the selected two-level scope, and a reversed group topology. -/
example :
    applicationError? (cleared 4 1) =
        some (.overCapacityTarget (address amount.id 4 1) 3) ∧
    applicationError? (cleared 1 5) =
        some (.overCapacityTarget (address amount.id 1 5) 4) ∧
    applicationError? { cleared 1 1 with
      targetField := { field := outerAmount.id, path := [1] }} =
        some (.invalidTwoLevelScope
          { field := outerAmount.id, path := [1] } 10 20) ∧
    topologyError? 20 10 = some (.unsupportedTwoLevelDestination 20 10) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.NestedApplication
