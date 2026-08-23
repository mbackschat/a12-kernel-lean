import A12Kernel.Elaboration.AddressedNumberBinary

/-! # Repeatable direct-Number binary arithmetic locks, including one outer-scope operand -/

namespace A12Kernel.Conformance.AddressedNumberBinary

open A12Kernel

private def number (id : FieldId) (name : String) (scale : Nat) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale, signed := true } }
  repeatableScope := [10]
}

private def left := number 1 "A" 1
private def right : FlatFieldDecl := {
  number 2 "B" 2 with
  numericTargetConstraints := { maximum := some 10 }
}
private def additive := number 3 "Additive" 2
private def product : FlatFieldDecl := {
  number 4 "Product" 3 with
  numericTargetConstraints := { maximum := some (9999 / 1000) }
}
private def wrongScale := number 5 "WrongScale" 1
private def outerLeft : FlatFieldDecl := {
  number 6 "Outer" 1 with groupPath := ["Probe"], repeatableScope := []
}

private def model : FlatModel := {
  fields := [left, right, additive, product, wrongScale, outerLeft]
  repeatableGroups := [{
    level := 10
    path := ["Probe", "Rows"]
    repeatability := some 7
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def cell (field : FieldId) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored, raw }

private def decimalCell (field : FieldId) (row : Nat) (stored : String)
    (unscaled scale : Int) (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [row] }
  stored
  raw
  numericDecimal := some { unscaled, scale }
}

private def input? (extra : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range 7).map fun i =>
      { group := 10, path := [i + 1] }
    cells := [
      cell left.id 1 "3.5" (.parsed (.num (7 / 2))),
      cell right.id 1 "1.25" (.parsed (.num (5 / 4))),
      cell right.id 2 "5.25" (.parsed (.num (21 / 4))),
      cell left.id 3 "-2" (.parsed (.num (-2))),
      cell left.id 5 "bad-left" (.rejected .malformed),
      cell right.id 5 "12" (.rejected .declaredConstraint),
      cell left.id 6 "4" (.parsed (.num 4)),
      cell right.id 6 "12" (.rejected .declaredConstraint),
      cell left.id 7 "4" (.parsed (.num 4)),
      cell right.id 7 "3" (.parsed (.num 3))
    ] ++ extra
  }).toOption

private def operation? (target : FlatFieldDecl) (op : NumericArithmeticOp) :
    Option (CheckedAddressedNumberBinary model) :=
  (checkAddressedNumberBinary model ["Probe", "Rows"] target.id
    (bare "A") (bare "B") op).toOption

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def outcomes? (target : FlatFieldDecl) (op : NumericArithmeticOp) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation? target op
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def result? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation? product .multiply
  let input ← input? extra
  (operation.executeResult input (fun _ => ()) []).toOption

example :
    (operation? additive .add).isSome = true ∧
    (operation? additive .subtract).isSome = true ∧
    (operation? product .multiply).isSome = true ∧
    (match checkAddressedNumberBinary model ["Probe", "Rows"]
        wrongScale.id (bare "A") (bare "B") .multiply with
      | .error (.scaleMismatch 1 3) => true
      | _ => false) = true := by
  native_decide

example : outcomes? additive .add = some [
    (addr additive.id 1, .accepted (stored 475 2)),
    (addr additive.id 2, .accepted (stored 525 2)),
    (addr additive.id 3, .accepted (stored (-2) 0)),
    (addr additive.id 4, .accepted (stored 0 0)),
    (addr additive.id 5, .inheritedPoison .malformed),
    (addr additive.id 6, .inheritedPoison .declaredConstraint),
    (addr additive.id 7, .accepted (stored 7 0))
  ] := by native_decide

example : outcomes? additive .subtract = some [
    (addr additive.id 1, .accepted (stored 225 2)),
    (addr additive.id 2, .accepted (stored (-525) 2)),
    (addr additive.id 3, .accepted (stored (-2) 0)),
    (addr additive.id 4, .accepted (stored 0 0)),
    (addr additive.id 5, .inheritedPoison .malformed),
    (addr additive.id 6, .inheritedPoison .declaredConstraint),
    (addr additive.id 7, .accepted (stored 1 0))
  ] := by native_decide

example : outcomes? product .multiply = some [
    (addr product.id 1, .accepted (stored 4375 3)),
    (addr product.id 2, .accepted (stored 0 0)),
    (addr product.id 3, .accepted (stored 0 0)),
    (addr product.id 4, .accepted (stored 0 0)),
    (addr product.id 5, .inheritedPoison .malformed),
    (addr product.id 6, .inheritedPoison .declaredConstraint),
    (addr product.id 7, .rejected (stored 12 0) .aboveMaximum)
  ] := by native_decide

example :
    (do
      let view ← result? [
        decimalCell product.id 1 "4.375" 4375 3 (.parsed (.num (35 / 8))),
        decimalCell product.id 2 "1.000" 1000 3 (.parsed (.num 1)),
        decimalCell product.id 5 "7.000" 7000 3 (.parsed (.num 7))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField))) =
      some (
        [addr product.id 2, addr product.id 3, addr product.id 4],
        [addr product.id 5],
        [addr product.id 7]) := by
  native_decide

private def outerPairOutcomes? :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ←
    (checkAddressedNumberBinary model ["Probe", "Rows"] additive.id
      (parent "Outer") (bare "B") .add).toOption
  let input ← input? [
    { address := { field := outerLeft.id, path := [] }, stored := "0.5"
      raw := .parsed (.num (1 / 2)) }]
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

/- The pair reads each operand at its **own** scope: the outer left operand resolves once at the
document root and combines with every row's own right operand. This is the second independent read
site the widening touched, and borrowing the target's path here would have read the outer operand as
empty in every row. -/
example : outerPairOutcomes? = some [
    (addr additive.id 1, .accepted (stored 175 2)),
    (addr additive.id 2, .accepted (stored 575 2)),
    (addr additive.id 3, .accepted (stored 5 1)),
    (addr additive.id 4, .accepted (stored 5 1)),
    (addr additive.id 5, .inheritedPoison .declaredConstraint),
    (addr additive.id 6, .inheritedPoison .declaredConstraint),
    (addr additive.id 7, .accepted (stored 35 1))
  ] := by native_decide

end A12Kernel.Conformance.AddressedNumberBinary
