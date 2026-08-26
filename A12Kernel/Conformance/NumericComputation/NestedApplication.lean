import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Semantics.NumericComparison

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

private def positiveRows
    (projection : NumericComputationTwoLevelApplicationProjection model) :
    Option (List CellAddr) :=
  projection.leafRows.foldlM (init := []) fun fired row => do
    let [outer, inner] := row.path | none
    let target := address amount.id outer inner
    match projection.stateAt target with
    | .absent | .presentEmpty => some fired
    | .presentValue (.decimal number) =>
        if NumericComparisonOp.greater.evalFixedRight
            (.value number.amount .fixed) 0 == .fired .value then
          some (fired ++ [target])
        else some fired
    | .presentValue .nonComputedForm => none

private def laterValidation? : Option (List CellAddr) := do
  let destination ← empty?
  let applied ← (view [value 1 2 5, value 3 4 7])
    |>.applyToCheckedTwoLevel destination 10 20 |>.toOption
  positiveRows applied

/- Later validation is explicit and sees only the two positive applied values, not their padded predecessors. -/
example : laterValidation? = some [address amount.id 1 2, address amount.id 3 4] := by
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
