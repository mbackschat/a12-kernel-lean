import A12Kernel.Elaboration.AddressedRangeAsNumber

/-! # Addressed `RangeAsNumber` locks

The matrix retains one exact 1-based inclusive interval while separating selected digits, filled fallback zero, missing zero, row-local formal poison, Number target rejection, and exact result addresses.
-/

namespace A12Kernel.Conformance.AddressedRangeAsNumber

open A12Kernel

private def code : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Code"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 5 }
  repeatableScope := [10]
}

private def amount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order", "Rows"]
  name := "Amount"
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some 99 }
  repeatableScope := [10]
}

private def outerCode : FlatFieldDecl := {
  code with
    id := 3
    groupPath := ["Order"]
    name := "OuterCode"
    repeatableScope := []
}

private def wrong : FlatFieldDecl := {
  amount with
    id := 4
    name := "Wrong"
}

private def scaledAmount : FlatFieldDecl := {
  amount with
    id := 5
    name := "ScaledAmount"
    policy := { kind := .number { scale := 2, signed := false } }
}

private def widerAmount : FlatFieldDecl := {
  amount with
    id := 6
    name := "WiderAmount"
    policy := { kind := .number { scale := 4, signed := false } }
}

private def model : FlatModel := {
  fields := [code, amount, outerCode, wrong, scaledAmount, widerAmount]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Rows"]
    repeatability := some 3
  }]
}

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedRangeAsNumber model) :=
  (checkAddressedRangeAsNumber
    model ["Order", "Rows"] amount.id (bare "Code") 2 4).toOption

private def rows : List RowAddr :=
  [{ group := 10, path := [1] },
   { group := 10, path := [2] },
   { group := 10, path := [3] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells
  }).toOption

private def outcomes?
    (cells : List ClassifiedCellInput)
    (targetField : FieldId := amount.id) (suppress : Bool := false) :
    Option (List (SourcedNumericTargetOutcome CellAddr)) := do
  let operation ← (checkAddressedRangeAsNumber
    model ["Order", "Rows"] targetField (bare "Code") 2 4 suppress).toOption
  let input ← checkedDocument cells
  (operation.execute input).toOption

private def result?
    (cells : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation?
  let input ← checkedDocument cells
  (operation.executeResult input (fun _ => ()) []).toOption

private def addressAt (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) : StoredNumber :=
  { unscaled, scale := 0 }

/- Exact interval and source-kind admission remain independent of source placement. -/
example :
    (operation?.map fun operation => (operation.start, operation.finish)) =
      some (2, 4) ∧
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] amount.id (bare "Code") 0 4 with
      | .error (.invalidRange 0 4) => true
      | _ => false) = true ∧
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] amount.id (bare "Wrong") 2 4 with
      | .error (.sourceNotEvaluatedString path) => path == wrong.path
      | _ => false) = true ∧
    (checkAddressedRangeAsNumber
      model ["Order", "Rows"] amount.id (parent "OuterCode") 2 4).isOk =
        true := by
  native_decide

example :
    (checkAddressedRangeAsNumber
      model ["Order", "Rows"] scaledAmount.id (bare "Code") 2 4 true).isOk = true ∧
    (checkAddressedRangeAsNumber
      model ["Order", "Rows"] widerAmount.id (bare "Code") 2 4 true).isOk = true ∧
    (checkAddressedRangeAsNumber
      model ["Order", "Rows"] scaledAmount.id (bare "Code") 2 2 true).isOk = true ∧
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] scaledAmount.id (bare "Code") 2 4 with
      | .error (.scaleMismatch 2 0) => true
      | _ => false) = true ∧
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] widerAmount.id (bare "Code") 2 4 with
      | .error (.scaleMismatch 4 0) => true
      | _ => false) = true ∧
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] scaledAmount.id (bare "Wrong") 2 4 true with
      | .error (.sourceNotEvaluatedString path) => path == wrong.path
      | _ => false) = true ∧
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] scaledAmount.id (bare "Code") 0 4 true with
      | .error (.invalidRange 0 4) => true
      | _ => false) = true := by
  native_decide

example :
    (match checkAddressedRangeAsNumber
        model ["Order", "Rows"] amount.id (bare "Code") 2 4 true with
      | .ok operation =>
        operation.suppressExactScaleWarning && operation.start == 2 && operation.finish == 4
      | .error _ => false) = true ∧
    (match operation? with
      | some operation => !operation.suppressExactScaleWarning
      | none => false) = true := by
  native_decide

/- Selection is 1-based and inclusive: `A012B[2..4]` is `012` and therefore 12; a filled nondigit selection and a missing source both produce real zero. -/
example :
    [(amount.id, false), (scaledAmount.id, true)].all (fun (targetField, suppress) =>
      decide ((outcomes? [
        cell code.id [1] "A012B" (.parsed (.str "A012B")),
        cell code.id [2] "A1XB" (.parsed (.str "A1XB"))
      ] targetField suppress).map (·.map fun entry => (entry.targetField, entry.outcome)) =
        some [
          (addressAt targetField 1, .accepted (stored 12)),
          (addressAt targetField 2, .accepted (stored 0)),
          (addressAt targetField 3, .accepted (stored 0))
        ])) = true := by
  native_decide

/- Formal invalidity remains row-local poison, while a neighboring three-digit selection survives as a payloadful target rejection. -/
example :
    [(amount.id, false), (scaledAmount.id, true)].all (fun (targetField, suppress) =>
      decide ((outcomes? [
        cell code.id [1] "TOO-LONG" (.parsed (.str "TOO-LONG")),
        cell code.id [2] "A123B" (.parsed (.str "A123B")),
        cell code.id [3] "A012B" (.parsed (.str "A012B"))
      ] targetField suppress).map (·.map fun entry => (entry.targetField, entry.outcome)) =
        some [
          (addressAt targetField 1, .inheritedPoison .declaredConstraint),
          (addressAt targetField 2, .rejected (stored 123) .aboveMaximum),
          (addressAt targetField 3, .accepted (stored 12))
        ])) = true := by
  native_decide

/- Result classification keeps exact row keys: poison clears a stale first-row target, target rejection errors at row two, and accepted row three remains source-classified changed. -/
example :
    (do
      let view ← result? [
        cell code.id [1] "TOO-LONG" (.parsed (.str "TOO-LONG")),
        cell amount.id [1] "9" (.parsed (.num 9)),
        cell code.id [2] "A123B" (.parsed (.str "A123B")),
        cell code.id [3] "A012B" (.parsed (.str "A012B"))
      ]
      pure (view.cleared, view.withChanges.map
        fun entry => (entry.targetField, entry.value), view.withErrors)) =
      some (
        [addressAt amount.id 1],
        [(addressAt amount.id 3, stored 12)],
        [{
          targetField := addressAt amount.id 2
          attempted := stored 123
          cause := .aboveMaximum
        }]) := by
  native_decide

end A12Kernel.Conformance.AddressedRangeAsNumber
