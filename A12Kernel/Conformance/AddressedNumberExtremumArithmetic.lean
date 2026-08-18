import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Operand-local field-pair arithmetic inside same-scope repeatable Number extrema -/

namespace A12Kernel.Conformance.AddressedNumberExtremumArithmetic

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
private def widePrecision := number 7 "WidePrecision" 4
/- A summed-scale target with a maximum, so a product-driven target rejection stays observable. -/
private def cappedPrecise : FlatFieldDecl := {
  number 8 "CappedPrecise" 3 with
  numericTargetConstraints := { maximum := some (9999 / 1000) }
}

private def zeroScale := number 9 "ZeroScale" 0

private def model : FlatModel := {
  fields := [left, right, direct, target, preciseTarget, wrongScale,
    widePrecision, cappedPrecise, zeroScale]
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

private def fld (name : String) : SurfaceAddressedNumberArithmeticOperand :=
  .field (bare name)

private def lit (value : Rat) (authoredScale : Int) :
    SurfaceAddressedNumberArithmeticOperand :=
  .literal { value, authoredScale }

private def arith (op : NumericArithmeticOp)
    (left right : SurfaceAddressedNumberArithmeticOperand) :
    SurfaceAddressedNumberExtremumOperand :=
  .arithmetic op left right

private def addition (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  arith .add (fld left) (fld right)

private def subtraction (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  arith .subtract (fld left) (fld right)

private def multiplication (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  arith .multiply (fld left) (fld right)

private def nestedExtremum (op : NumericExtremumOp)
    (first : SurfaceAddressedNumberArithmeticOperand)
    (rest : List SurfaceAddressedNumberArithmeticOperand) :
    SurfaceAddressedNumberExtremumOperand :=
  .extremum op first rest

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

/- A summed-scale product needs a target other than the shared scale-2 one, so this run names both its target and its extremum operation. -/
private def outcomesInto? (targetField : FlatFieldDecl)
    (op : NumericExtremumOp)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← (checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
    targetField.id first rest op).toOption
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
      | .error (.scaleMismatch 1 summary) =>
          summary.scale == ScaleInfo.exact 2
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
      | .error (.scaleMismatch 1 summary) =>
          summary.scale == ScaleInfo.exact 2
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

/- Multiplication derives the SUM of its inner source scales, so it cannot ride the additive tag's maximum-scale contract. Its accepted target is scale 3 while the same operands under addition target scale 2. -/
example :
    (operation? preciseTarget (multiplication "A" "B") [field "C"]).isSome = true ∧
    (operation? preciseTarget (field "C") [multiplication "A" "B"]).isSome = true ∧
    (operation? preciseTarget (multiplication "B" "A") [field "C"]).isSome = true ∧
    (operation? widePrecision (multiplication "A" "B")
      [field "C", literal (5 / 4) 4]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        target.id (multiplication "A" "B") [field "C"] .minimum with
      | .error (.scaleMismatch 2 summary) =>
          summary.scale == ScaleInfo.exact 3
      | _ => false) = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        widePrecision.id (multiplication "A" "B") [field "C"] .minimum with
      | .error (.scaleMismatch 4 summary) =>
          summary.scale == ScaleInfo.exact 3
      | _ => false) = true ∧
    (operation? preciseTarget (multiplication "PreciseTarget" "A")
      [field "C"]).isNone = true := by
  native_decide

/- Multiplication delegates the shared pair's empty-as-zero and inner first-poison rules before the outer minimum selects in authored order. -/
example : outcomesInto? preciseTarget .minimum (multiplication "A" "B")
    [field "C"] = some [
    (addr preciseTarget.id 1, .accepted (stored 3375 3)),
    (addr preciseTarget.id 2, .accepted (stored (-2) 0)),
    (addr preciseTarget.id 3, .accepted (stored 0 0)),
    (addr preciseTarget.id 4, .accepted (stored 0 0)),
    (addr preciseTarget.id 5, .accepted (stored 0 0)),
    (addr preciseTarget.id 6, .inheritedPoison .malformed),
    (addr preciseTarget.id 7, .inheritedPoison .declaredConstraint),
    (addr preciseTarget.id 8, .accepted (stored 20 0))
  ] := by
  native_decide

/- Under the maximum fold the product itself wins rows 2 and 8, so an ordinary summed-scale target policy rejects the product rather than a direct field. -/
example : outcomesInto? cappedPrecise .maximum (multiplication "A" "B")
    [field "C"] = some [
    (addr cappedPrecise.id 1, .accepted (stored 5 0)),
    (addr cappedPrecise.id 2, .rejected (stored 20 0) .aboveMaximum),
    (addr cappedPrecise.id 3, .accepted (stored 5 0)),
    (addr cappedPrecise.id 4, .accepted (stored 5 0)),
    (addr cappedPrecise.id 5, .accepted (stored 5 0)),
    (addr cappedPrecise.id 6, .inheritedPoison .malformed),
    (addr cappedPrecise.id 7, .inheritedPoison .declaredConstraint),
    (addr cappedPrecise.id 8, .rejected (stored 120 0) .aboveMaximum)
  ] := by
  native_decide

/- An immediate literal is admitted at either inner position of the arithmetic child, and the child's derived scale consumes the literal's AUTHORED scale through the same operation rule: `1.5` contributes scale 1 and `1.50` contributes scale 2, so the identical value changes the legal target. -/
example :
    (operation? preciseTarget (arith .multiply (fld "A") (lit (3 / 2) 1))
      [field "C"]).isSome = true ∧
    (operation? preciseTarget (arith .multiply (lit (3 / 2) 1) (fld "A"))
      [field "C"]).isSome = true ∧
    (operation? widePrecision (arith .multiply (fld "A") (lit (3 / 2) 2))
      [field "C"]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        preciseTarget.id (arith .multiply (fld "A") (lit (3 / 2) 2))
        [field "C"] .minimum with
      | .error (.scaleMismatch 3 summary) =>
          summary.scale == ScaleInfo.exact 4
      | _ => false) = true ∧
    (operation? target (arith .add (fld "A") (lit (3 / 2) 1))
      [field "C"]).isSome = true := by
  native_decide

/- The child's literal does not consume the outer list's one-literal budget, and that outer budget stays exactly one. A child of two literals is admitted, since the target's own certificate owns iteration. -/
example :
    (operation? preciseTarget (arith .multiply (fld "A") (lit (3 / 2) 1))
      [field "C", literal 2 0]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        preciseTarget.id (arith .multiply (fld "A") (lit (3 / 2) 1))
        [field "C", literal 2 0, literal 3 0] .minimum with
      | .error .tooManyLiterals => true
      | _ => false) = true := by
  native_decide

/- The literal replaces the second field entirely, so row 7 — whose `B` is target-rejected — is now clean: a retained child reads only its own dependencies. Empty times a literal is still zero, and a malformed source still poisons. -/
example : outcomesInto? preciseTarget .minimum
    (arith .multiply (fld "A") (lit (3 / 2) 1)) [field "C"] = some [
    (addr preciseTarget.id 1, .accepted (stored 3375 3)),
    (addr preciseTarget.id 2, .accepted (stored (-2) 0)),
    (addr preciseTarget.id 3, .accepted (stored 0 0)),
    (addr preciseTarget.id 4, .accepted (stored 3 0)),
    (addr preciseTarget.id 5, .accepted (stored 0 0)),
    (addr preciseTarget.id 6, .inheritedPoison .malformed),
    (addr preciseTarget.id 7, .accepted (stored (-9) 0)),
    (addr preciseTarget.id 8, .accepted (stored 20 0))
  ] := by
  native_decide

/- Multiplication cannot separate the inner positions by value, so subtraction is the witness that authored inner order is retained through execution, not merely through identity. -/
example :
    (outcomesInto? target .minimum (arith .subtract (fld "A") (lit (3 / 2) 1))
      [field "C"] >>= List.head?) =
      some (addr target.id 1, .accepted (stored 75 2)) ∧
    (outcomesInto? target .minimum (arith .subtract (lit (3 / 2) 1) (fld "A"))
      [field "C"] >>= List.head?) =
      some (addr target.id 1, .accepted (stored (-75) 2)) := by
  native_decide

/- Target admission is the `==`/`!=` comparison predicate, not scale equality. An integer literal strips trailing zeros to a negative authored scale, so `[A] * 100` derives scale 0 while retaining multiplicative-constant capability through multiplication; that capable expression is admitted at its exact scale AND padded up to any larger declared scale. -/
example :
    (operation? zeroScale (arith .multiply (fld "A") (lit 100 (-2))) []).isSome = true ∧
    (operation? target (arith .multiply (fld "A") (lit 100 (-2))) []).isSome = true ∧
    (operation? widePrecision (arith .multiply (fld "A") (lit 100 (-2)))
      []).isSome = true := by
  native_decide

/- Padding is directional and capability is lost to any non-capable operand: a capable larger derived scale is still rejected at a smaller target, and one bare field operand collapses the list back to exact equality. -/
example :
    (operation? zeroScale (arith .multiply (fld "A") (lit (3 / 2) 2))
      []).isNone = true ∧
    (operation? target (arith .multiply (fld "A") (lit 100 (-2)))
      [field "C"]).isSome = true ∧
    (operation? widePrecision (arith .multiply (fld "A") (lit 100 (-2)))
      [field "C"]).isNone = true ∧
    (operation? zeroScale (arith .multiply (fld "A") (lit 100 (-2)))
      [field "C"]).isNone = true := by
  native_decide

/- A constant-only arithmetic child is admitted, and a list of only such operands needs no field reference at all. Its derived scale 1 stays capability-carrying, so it is padded up to declared scale 2 or 4 and still rejected at 0. -/
example :
    (operation? target (arith .multiply (lit (3 / 2) 1) (lit 2 0))
      [field "C"]).isSome = true ∧
    (operation? target (arith .multiply (lit (3 / 2) 1) (lit 2 0))
      []).isSome = true ∧
    (operation? widePrecision (arith .multiply (lit (3 / 2) 1) (lit 2 0))
      []).isSome = true ∧
    (operation? zeroScale (arith .multiply (lit (3 / 2) 1) (lit 2 0))
      []).isNone = true ∧
    (operation? target (arith .multiply (lit (3 / 2) 1) (lit 2 0))
      [literal 3 0]).isSome = true := by
  native_decide

/- A fieldless list still computes once per instantiated row, including rows whose every cell is absent, because repetition comes from the computed target's own declaration rather than from a source reference. -/
example : outcomesInto? target .minimum
    (arith .multiply (lit (3 / 2) 1) (lit 2 0)) [] =
    some ((List.range 8).map fun row =>
      (addr target.id (row + 1), .accepted (stored 3 0))) := by
  native_decide

/- Each nested call owns its immediate-literal budget. One literal inside the child and one at the outer call are admitted, while either call still rejects a second immediate literal of its own. The child remains one bounded outer operand rather than being flattened. -/
example :
    (operation? target
      (nestedExtremum .minimum (fld "A") [lit 1 0])
      [literal 2 0]).isSome = true ∧
    (operation? target
      (nestedExtremum .maximum (fld "A") [lit 1 0])
      [literal 2 0]).isSome = true ∧
    (operation? target (field "C")
      [nestedExtremum .minimum (fld "A") [lit 1 0]]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        target.id
        (nestedExtremum .minimum (fld "A") [lit 1 0, lit 2 0])
        [] .minimum with
      | .error .tooManyLiterals => true
      | _ => false) = true ∧
    (match checkAddressedNumberExtremumOperands model ["Probe", "Rows"]
        target.id (field "A") [literal 1 0, literal 2 0] .minimum with
      | .error .tooManyLiterals => true
      | _ => false) = true := by
  native_decide

/- The nested call contributes the union of its own leaf scales to the outer target check. A scale-4 literal beside scale-2 `A` therefore admits only the scale-4 target. -/
example :
    (operation? widePrecision
      (nestedExtremum .maximum (fld "A") [lit (3 / 2) 4]) []).isSome = true ∧
    (operation? target
      (nestedExtremum .maximum (fld "A") [lit (3 / 2) 4]) []).isNone = true := by
  native_decide

/- Outer authored order is independent of nested leaf order. Whichever outer operand is reached first supplies the row-6 poison, and placing the nested call second exercises the retained call as a rest operand. -/
example :
    (outcomes? (nestedExtremum .minimum (fld "B") [lit 1 0])
        [field "A"] >>= (·[5]?)) =
      some (addr target.id 6, .inheritedPoison .declaredConstraint) ∧
    (outcomes? (field "A")
        [nestedExtremum .minimum (fld "B") [lit 1 0]] >>= (·[5]?)) =
      some (addr target.id 6, .inheritedPoison .malformed) := by
  native_decide

/- Empty nested leaves retain the established extremum substitution law: each empty leaf contributes zero before the nested and outer selectors run. -/
example :
    (outcomes? (nestedExtremum .minimum (fld "A") [fld "B"])
        [field "C"] >>= (·[2]?)) =
      some (addr target.id 3, .accepted (stored 0 0)) ∧
    (outcomes? (nestedExtremum .minimum (fld "A") [fld "B"])
        [field "C"] >>= (·[4]?)) =
      some (addr target.id 5, .accepted (stored 0 0)) := by
  native_decide

/- The nested selector is executable semantics, not decoration: the same child values distinguish `Min` from `Max` before the outer minimum sees `C`. -/
example :
    (outcomes? (nestedExtremum .minimum (fld "A") [fld "B"])
        [field "C"] >>= List.head?) =
      some (addr target.id 1, .accepted (stored 15 1)) ∧
    (outcomes? (nestedExtremum .maximum (fld "A") [fld "B"])
        [field "C"] >>= List.head?) =
      some (addr target.id 1, .accepted (stored 225 2)) := by
  native_decide

/- Nested evaluation preserves authored leaf order: when both sources are poisoned on row 6, the first nested leaf supplies the inherited cause. -/
example :
    (outcomes? (nestedExtremum .minimum (fld "B") [fld "A"])
        [field "C"] >>= (·[5]?)) =
      some (addr target.id 6, .inheritedPoison .declaredConstraint) ∧
    (outcomes? (nestedExtremum .minimum (fld "A") [fld "B"])
        [field "C"] >>= (·[5]?)) =
      some (addr target.id 6, .inheritedPoison .malformed) := by
  native_decide

private inductive InnerShape where
  | field (field : FieldId)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

private inductive OperandShape where
  | field (field : FieldId)
  | arithmetic (operation : NumericArithmeticOp)
      (left right : InnerShape)
  | other
  deriving Repr, DecidableEq

private def innerShapes : CheckedAddressedNumberArithmeticChild model →
    InnerShape × InnerShape
  | .fields pair =>
      (.field pair.left.placement.sourceDeclaration.id,
        .field pair.right.placement.sourceDeclaration.id)
  | .fieldLiteral source decoded =>
      (.field source.placement.sourceDeclaration.id, .literal decoded)
  | .literalField decoded source =>
      (.literal decoded, .field source.placement.sourceDeclaration.id)
  | .literals left right => (.literal left, .literal right)

private def operandShape : CheckedAddressedNumberExtremumOperand model →
    OperandShape
  | .field source => .field source.placement.sourceDeclaration.id
  | .arithmetic operation child =>
      .arithmetic operation (innerShapes child).1 (innerShapes child).2
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
        [.arithmetic .add (.field right.id) (.field left.id), .field direct.id]) := by
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
        [.arithmetic .subtract (.field right.id) (.field left.id), .field direct.id]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberExtremumArithmetic
