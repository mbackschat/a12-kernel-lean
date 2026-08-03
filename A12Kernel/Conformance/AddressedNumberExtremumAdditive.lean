import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Operand-local additive arithmetic inside same-scope repeatable Number extrema -/

namespace A12Kernel.Conformance.AddressedNumberExtremumAdditive

open A12Kernel

private def number (id : FieldId) (name : String) (scale : Nat) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale, signed := true } }
  repeatableScope := [10]
}

private def left := number 1 "A" 2
private def right : FlatFieldDecl := {
  number 2 "B" 1 with
  numericTargetConstraints := { maximum := some 10 }
}
private def direct := number 3 "C" 2
private def target : FlatFieldDecl := {
  number 4 "Target" 2 with
  numericTargetConstraints := { maximum := some (999 / 100) }
}
private def preciseTarget := number 5 "PreciseTarget" 3
private def wrongScale := number 6 "WrongScale" 1

private def model : FlatModel := {
  fields := [left, right, direct, target, preciseTarget, wrongScale]
  repeatableGroups := [{
    level := 10
    path := ["Probe", "Rows"]
    repeatability := some 8
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def addition (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .addition (bare left) (bare right)

private def subtraction (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .subtraction (bare left) (bare right)

private def field (name : String) : SurfaceAddressedNumberExtremumOperand :=
  .field (bare name)

private def literal (value : Rat) (scale : Int) :
    SurfaceAddressedNumberExtremumOperand :=
  .literal { value, authoredScale := scale }

private def operation? (targetField : FlatFieldDecl)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (CheckedAddressedNumberExtremum model) :=
  (checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
    targetField.id first rest .minimum).toOption

private def maximumOperation? (targetField : FlatFieldDecl)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (CheckedAddressedNumberExtremum model) :=
  (checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
    targetField.id first rest .maximum).toOption

private def cell (fieldId : FieldId) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := fieldId, path := [row] }, stored, raw }

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range 8).map fun i =>
      { group := 10, path := [i + 1] }
    cells := [
      cell left.id 1 "2.25" (.parsed (.num (9 / 4))),
      cell right.id 1 "1.5" (.parsed (.num (3 / 2))),
      cell direct.id 1 "5" (.parsed (.num 5)),
      cell left.id 2 "5" (.parsed (.num 5)),
      cell right.id 2 "4" (.parsed (.num 4)),
      cell direct.id 2 "-2" (.parsed (.num (-2))),
      cell right.id 3 "2" (.parsed (.num 2)),
      cell direct.id 3 "5" (.parsed (.num 5)),
      cell left.id 4 "2" (.parsed (.num 2)),
      cell direct.id 4 "5" (.parsed (.num 5)),
      cell direct.id 5 "5" (.parsed (.num 5)),
      cell left.id 6 "bad-left" (.rejected .malformed),
      cell right.id 6 "12" (.rejected .declaredConstraint),
      cell direct.id 6 "-9" (.parsed (.num (-9))),
      cell left.id 7 "2" (.parsed (.num 2)),
      cell right.id 7 "12" (.rejected .declaredConstraint),
      cell direct.id 7 "-9" (.parsed (.num (-9))),
      cell left.id 8 "20" (.parsed (.num 20)),
      cell right.id 8 "6" (.parsed (.num 6)),
      cell direct.id 8 "20" (.parsed (.num 20))
    ]
  }).toOption

private def addr (fieldId : FieldId) (row : Nat) : CellAddr :=
  { field := fieldId, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def outcomes? (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation? target first rest
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun outcome => (outcome.targetField, outcome.outcome))

private def maximumOutcomes?
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← maximumOperation? target first rest
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun outcome => (outcome.targetField, outcome.outcome))

/- A field-pair addition is one bounded outer operand. Its result scale is the maximum inner source scale, while a literal sibling can raise the outer target scale. -/
example :
    (operation? target (addition "A" "B") [field "C"]).isSome = true ∧
    (operation? target (field "C") [addition "A" "B"]).isSome = true ∧
    (operation? target (addition "B" "A") [field "C"]).isSome = true ∧
    (operation? preciseTarget (addition "A" "B")
      [field "C", literal (5 / 4) 3]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        wrongScale.id (addition "A" "B") [field "C"] .minimum with
      | .error (.scaleMismatch 1 2) => true
      | _ => false) = true ∧
    (operation? target (addition "Target" "A") [field "C"]).isNone = true := by
  native_decide

/- Addition delegates empty-as-zero and inner first-poison behavior before the outer extremum selects in authored order. -/
example : outcomes? (addition "A" "B") [field "C"] = some [
    (addr target.id 1, .accepted (stored 375 2)),
    (addr target.id 2, .accepted (stored (-2) 0)),
    (addr target.id 3, .accepted (stored 2 0)),
    (addr target.id 4, .accepted (stored 2 0)),
    (addr target.id 5, .accepted (stored 0 0)),
    (addr target.id 6, .inheritedPoison .malformed),
    (addr target.id 7, .inheritedPoison .declaredConstraint),
    (addr target.id 8, .rejected (stored 20 0) .aboveMaximum)
  ] := by
  native_decide

/- The same operand-local addition reaches the shared maximum fold; the direct field wins the first row, separating this instance from the minimum result above. -/
example : (maximumOutcomes? (addition "A" "B") [field "C"]
    >>= List.head?) = some (addr target.id 1, .accepted (stored 5 0)) := by
  native_decide

/- A field-pair subtraction occupies the same bounded outer positions and derives the same maximum child scale, while preserving its distinct scalar identity and target exclusions. -/
example :
    (operation? target (subtraction "A" "B") [field "C"]).isSome = true ∧
    (operation? target (field "C") [subtraction "A" "B"]).isSome = true ∧
    (operation? target (subtraction "B" "A") [field "C"]).isSome = true ∧
    (operation? preciseTarget (subtraction "A" "B")
      [field "C", literal (5 / 4) 3]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        wrongScale.id (subtraction "A" "B") [field "C"] .minimum with
      | .error (.scaleMismatch 1 2) => true
      | _ => false) = true ∧
    (operation? target (subtraction "Target" "A") [field "C"]).isNone = true := by
  native_decide

/- Subtraction delegates the shared pair's empty-as-zero and inner first-poison rules before the outer minimum selects in authored order. -/
example : outcomes? (subtraction "A" "B") [field "C"] = some [
    (addr target.id 1, .accepted (stored 75 2)),
    (addr target.id 2, .accepted (stored (-2) 0)),
    (addr target.id 3, .accepted (stored (-2) 0)),
    (addr target.id 4, .accepted (stored 2 0)),
    (addr target.id 5, .accepted (stored 0 0)),
    (addr target.id 6, .inheritedPoison .malformed),
    (addr target.id 7, .inheritedPoison .declaredConstraint),
    (addr target.id 8, .rejected (stored 14 0) .aboveMaximum)
  ] := by
  native_decide

/- The same subtraction operand reaches the shared maximum fold; the direct field wins the first row and separates maximum from minimum. -/
example : (maximumOutcomes? (subtraction "A" "B") [field "C"]
    >>= List.head?) = some (addr target.id 1, .accepted (stored 5 0)) := by
  native_decide

private inductive OperandShape where
  | field (field : FieldId)
  | additive (operation : AddressedNumberExtremumAdditiveOperation)
      (left right : FieldId)
  | other
  deriving Repr, DecidableEq

private def operandShape : CheckedAddressedNumberExtremumOperand model →
    OperandShape
  | .field source => .field source.placement.sourceDeclaration.id
  | .additive operation pair =>
      .additive operation pair.left.placement.sourceDeclaration.id
      pair.right.placement.sourceDeclaration.id
  | _ => .other

/- Reversing only the inner operands changes the first inherited cause when both sources are poisoned, while retaining the outer operand position exactly. -/
example :
    (do
      let operation ← operation? target (addition "B" "A") [field "C"]
      let input ← input?
      let outcomes ← (operation.execute input).toOption
      pure (outcomes[5]?.map (·.outcome),
        operation.orderedOperands.map operandShape)) =
      some (some (.inheritedPoison .declaredConstraint),
        [.additive .add right.id left.id, .field direct.id]) := by
  native_decide

/- Subtraction retains its distinct tag and reversed inner order, so the same first-cause separator remains visible to execution and Analyze consumers. -/
example :
    (do
      let operation ← operation? target (subtraction "B" "A") [field "C"]
      let input ← input?
      let outcomes ← (operation.execute input).toOption
      pure (outcomes[5]?.map (·.outcome),
        operation.orderedOperands.map operandShape)) =
      some (some (.inheritedPoison .declaredConstraint),
        [.additive .subtract right.id left.id, .field direct.id]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberExtremumAdditive
